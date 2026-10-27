module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2V

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem EndB.conj_mem_of_relIndex_two {G : Type*} [Group G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (h : Q.relIndex P = 2) {g q : G} (hg : g ∈ P) (hq : q ∈ Q) : g * q * g⁻¹ ∈ Q := by
  have hn : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two h
  have := hn.conj_mem ⟨q, hQP hq⟩ hq ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem Setting46e.card_closure_beta_z (hs : Setting46e t L p f S w z V i j) :
    4 ≤ Nat.card ↥(closure ({β₀, z} : Set X)) := by
  have hβ2 : β₀ * β₀ = 1 := by rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  have hzβ : z ∉ zpowers β₀ := fun h => by
    rcases L415.mem_zpowers_two hβ2 h with h1 | h1
    · exact hs.setup.z_ne_one h1
    · exact hs.setup.beta_ne_z hs.beta h1.symm
  have hβzc : β₀ * z = z * β₀ :=
    (mem_centralizer_singleton_iff.mp (K_le_centralizer_beta i j hs.lemma45.z_mem.2)).symm
  obtain ⟨-, -, h⟩ := L415.elem_sup (L415.elem_zpowers hβ2).1 (L415.elem_zpowers hβ2).2 hz2
    hzβ fun a ha => by
      rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl
      · group
      · exact hβzc
  rw [L415.card_zpowers_two hβ2 hs.beta.ne_one] at h
  have hle : zpowers β₀ ⊔ zpowers z ≤ closure ({β₀, z} : Set X) :=
    sup_le (zpowers_le.mpr (subset_closure (Set.mem_insert _ _)))
      (zpowers_le.mpr (subset_closure (Set.mem_insert_of_mem _ rfl)))
  have := Subgroup.card_le_of_le hle
  omega

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
local notation "A₀" => (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X)

theorem eq_U_of_not_mem_center (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W)
    (hV : IsSylowOf 2 V ⊤) (hβ : β₀ ∉ V ⊓ centralizer (V : Set X)) :
    W = V ⊓ centralizer ({β₀} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZV := Subgroup.card_le_of_le (hs.center_V_le_of_not_mem hKC hβ)
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  rw [L415.card_zpowers_two hz2 hs.setup.z_ne_one] at hZV
  have hZW := hs.card_closure_beta_z
  rw [← hc.center_eq hKC] at hZW
  have hWV : Nat.card W < Nat.card V := by
    have hle : Nat.card W ≤ Nat.card V :=
      (card_le_twoPart hc.sylow.isPGroup le_top).trans_eq hV.card_eq.symm
    refine lt_of_le_of_ne hle fun h => ?_
    have hWs : IsSylowOf 2 W ⊤ := isSylowOf_of_card le_top (h.trans hV.card_eq)
    have := EndB.card_center_le_of_isSylowOf hV hWs
    omega
  obtain ⟨a, ha⟩ := hc.sylow.isPGroup.exists_card_eq
  obtain ⟨b, hb⟩ := hs.sylow_V.isPGroup.exists_card_eq
  have h2W : 2 * Nat.card W ≤ Nat.card V := by
    rw [ha, hb] at hWV ⊢
    have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hWV
    calc 2 * 2 ^ a = 2 ^ (a + 1) := by ring
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  have hU := Subgroup.relIndex_mul_card (V ⊓ centralizer ({β₀} : Set X)) V
  rw [inf_of_le_left inf_le_left] at hU
  have hUi := hs.beta.relIndex_le
  have hUV : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ centralizer ({β₀} : Set X)) := by
    rw [← hU]
    exact Nat.mul_le_mul_right _ hUi
  exact (Subgroup.eq_of_le_of_card_ge hc.le (by omega)).symm

theorem false_of_not_mem_center (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W) (hV : IsSylowOf 2 V ⊤)
    (hβ : β₀ ∉ V ⊓ centralizer (V : Set X)) (hSV : S.relIndex V = 4) : False := by
  have hWU := hc.eq_U_of_not_mem_center hKC hV hβ
  have hWV : W ≤ V := hWU ▸ inf_le_left
  have hβV : β₀ ∈ V := hs.le_V (hs.setup.T_le (hs.setup.X_le_T (beta_mem_X i j)))
  have hidx : W.relIndex V = 2 := by
    rw [hWU]
    refine le_antisymm hs.beta.relIndex_le ?_
    by_contra hlt
    push Not at hlt
    have hne0 : (V ⊓ centralizer ({β₀} : Set X)).relIndex V ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (V ⊓ centralizer ({β₀} : Set X)) V
      rw [h0, zero_mul] at this
      exact (Nat.card_pos (α := V)).ne' this.symm
    have h1 : (V ⊓ centralizer ({β₀} : Set X)).relIndex V = 1 := by omega
    apply hβ
    refine ⟨hβV, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := (Subgroup.relIndex_eq_one.mp h1 hv).2
    exact (mem_centralizer_singleton_iff.mp this)
  have htX : t ∈ X₈ := subset_closure (by simp)
  have hnc := hc.qd_not_cyclic hSV
  have h4 : Nat.card ↥(Q₀) = 4 := hc.card_qTilde_eq_four hnc (hc.card_qTilde_le_four
    fun y hy => (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X
      (hs.sylow_V.le (hWV (hc.qTilde_le hy)))) t).mp htX)
  have h4' : Nat.card ↥(pCore 2 (MBar β₀)) = 4 := by rw [← hc.card_qTilde, h4]
  have hQ2 := fun q (hq : q ∈ Q₀) => hc.qTilde_sq h4 hnc hq
  obtain ⟨hAc, hA2, hA8⟩ := hc.A_elem hKC h4 hQ2
  have hAW : A₀ ≤ W := sup_le hc.qTilde_le (zpowers_le.mpr hc.z_mem_W)
  have hconj : ∀ g y : X, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun g y => rfl
  have hVA : ∀ v ∈ V, ∀ a ∈ A₀, v * a * v⁻¹ ∈ A₀ := by
    intro v hv a ha
    have hYW : (A₀).map (MulAut.conj v).toMonoidHom ≤ W := by
      rintro _ ⟨b, hb, rfl⟩
      rw [hconj]
      exact EndB.conj_mem_of_relIndex_two hWV hidx hv (hAW hb)
    have hYn : ∀ g ∈ W, ∀ y ∈ (A₀).map (MulAut.conj v).toMonoidHom,
        g * y * g⁻¹ ∈ (A₀).map (MulAut.conj v).toMonoidHom := by
      rintro g hg _ ⟨b, hb, rfl⟩
      have hg' : v⁻¹ * g * v ∈ W := by
        have := EndB.conj_mem_of_relIndex_two hWV hidx (V.inv_mem hv) hg
        rwa [inv_inv] at this
      refine ⟨(v⁻¹ * g * v) * b * (v⁻¹ * g * v)⁻¹, hc.A_normal hKC hg' hb, ?_⟩
      rw [hconj, hconj]
      group
    have hY2 : ∀ y ∈ (A₀).map (MulAut.conj v).toMonoidHom, y * y = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, hA2 b hb, map_one]
    have hYc : ∀ x ∈ (A₀).map (MulAut.conj v).toMonoidHom,
        ∀ y ∈ (A₀).map (MulAut.conj v).toMonoidHom, x * y = y * x := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hAc b hb b' hb']
    have hY8 : Nat.card ↥((A₀).map (MulAut.conj v).toMonoidHom) = 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj v).injective, hA8]
    have hYN := hc.le_N0_of_normal hKG hKC hFC hYW hYn hY2
    rcases hc.eq_X_or_eq_A hKC h4' hQ2 hYN hYc hY2 hY8 with h | h
    · exfalso
      have hvt : v * t * v⁻¹ ∈ (A₀).map (MulAut.conj v).toMonoidHom := by
        rw [h]
        exact (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X
          (hs.sylow_V.le hv)) t).mp htX
      obtain ⟨b, hb, hbt⟩ := hvt
      rw [hconj] at hbt
      have : b = t := by
        have := congrArg (fun y => v⁻¹ * y * v) hbt
        simpa [mul_assoc] using this
      exact hc.t_not_mem_A hKC (this ▸ hb)
    · rw [← h]
      exact ⟨a, ha, rfl⟩
  obtain ⟨y₀, hy₀, -, hty₀⟩ := hc.exists_y0 h4
  have hβe : β₀ = y₀⁻¹ * (t * y₀ * t⁻¹) := by rw [hty₀]; group
  apply hβ
  refine ⟨hβV, mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hvT : v * t * v⁻¹ ∈ W := by
    have := (mem_normalizer_iff.mp (hs.sylow_V.le hv) t).mp (mem_sup_left (mem_sup_left
      (mem_zpowers t)))
    exact hc.T_le this
  have hva : v * y₀ * v⁻¹ ∈ A₀ := hVA v hv y₀ (mem_sup_left hy₀)
  have hm := hc.A_comm_mem hKC h4 hvT hva
  have hvaW := hAW hva
  have h1 : v * β₀ * v⁻¹ = (v * y₀ * v⁻¹)⁻¹ *
      ((v * t * v⁻¹) * (v * y₀ * v⁻¹) * (v * t * v⁻¹)⁻¹ * (v * y₀ * v⁻¹)⁻¹) *
      (v * y₀ * v⁻¹)⁻¹⁻¹ := by
    rw [hβe]
    group
  have h2 : v * β₀ * v⁻¹ ∈ zpowers β₀ := by
    rw [h1, hc.conj_zpowers_eq (W.inv_mem hvaW) hm]
    exact hm
  rcases L415.mem_zpowers_two hc.beta_sq h2 with h3 | h3
  · exfalso
    apply hs.beta.ne_one
    have := congrArg (fun y => v⁻¹ * y * v) h3
    simpa [mul_assoc] using this
  · calc v * β₀ = v * β₀ * v⁻¹ * v := by group
      _ = β₀ * v := by rw [h3]

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
