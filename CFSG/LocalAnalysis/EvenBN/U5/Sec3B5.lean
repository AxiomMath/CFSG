module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3VThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo oTwo_le le_normalizer_oTwo isPGroup_oTwo
  crossedHom mem_ker_crossedHom crossed_conj)

theorem two_pow_ne_orbit {f m : ℕ} (hf : 2 ≤ f) :
    2 ^ m ≠ (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) + 1 ∧
      2 ^ m ≠ (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) + 1 := by
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨p, hp⟩ : ∃ p, 2 ^ f = p + 1 := ⟨2 ^ f - 1, by omega⟩
  rw [hp, Nat.add_sub_cancel]
  have hp3 : 3 ≤ p := by omega
  constructor
  · intro e
    have e' : 2 ^ m = (p + 1) * (p * (p + 1) + 1) := by rw [e]; ring
    have hdvd : p * (p + 1) + 1 ∣ 2 ^ m := Dvd.intro_left _ e'.symm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hodd : Odd (p * (p + 1) + 1) := (Nat.even_mul_succ_self p).add_one
    rw [hj] at hodd
    rcases j with _ | j
    · rw [pow_zero] at hj
      have : p * (p + 1) = 0 := by omega
      rcases Nat.mul_eq_zero.1 this with h0 | h0 <;> omega
    · exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (Nat.succ_ne_zero j)).2 even_two)
  · intro e
    have hodd : Odd (2 ^ m) := by
      rw [e]
      exact ((Nat.even_mul_succ_self p).mul_right _).add_one
    rcases m with _ | m
    · rw [pow_zero] at e
      have : p * (p + 1) * ((p + 1) ^ 2 + 1) = 0 := by omega
      simp at this
      omega
    · exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (Nat.succ_ne_zero m)).2 even_two)

namespace Data

section Def

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def B₅ (d : Data G h) : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer (d.B₁ : Set G))

end Def

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem B₅_eq_oTwo (d : Data G h) : d.B₅ = oTwo (normalizer (d.B₁ : Set G)) :=
  pCore_map_eq_oTwo _

theorem Hyp.mem_B₃_of_pow (hd : d.Hyp) {x : G} (hx : x ∈ centralizer (d.B₁ : Set G)) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ d.B₃ := by
  have htx : x ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hx d.t (mem_sup_left (mem_zpowers _))).symm
  have hxN : x ∈ normalizer (d.L : Set G) := hd.centralizer_le_normalizer htx
  have h2 : ∃ k : ℕ, d.act ⟨x, hxN⟩ ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨x, hxN⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  have hcomm : ∀ w ∈ Vh h, d.act ⟨x, hxN⟩ * w = w * d.act ⟨x, hxN⟩ := by
    intro w hw
    rw [← d.actImage_A₁, mem_actImage] at hw
    obtain ⟨a, haA, haN, rfl⟩ := hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 hx a (mem_sup_right haA)).symm
  have hS := twoCentralizerV h hd.two_le hd.center_hypPSU _ h2 hcomm
  rw [← d.actImage_A₃, mem_actImage] at hS
  obtain ⟨y, hyA, hyN, hy⟩ := hS
  have hyx : y⁻¹ * x ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨y⁻¹ * x, mul_mem (inv_mem hyN) hxN⟩).1 ?_
    have : (⟨y⁻¹ * x, mul_mem (inv_mem hyN) hxN⟩ : normalizer (d.L : Set G)) =
        (⟨y, hyN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨x, hxN⟩ := rfl
    rw [this, map_mul, map_inv, hy, inv_mul_cancel]
  have hyxt : y⁻¹ * x ∈ centralizer ({d.t} : Set G) :=
    mul_mem (inv_mem (hd.L_le_centralizer (d.A₃_le_P.trans d.P_le_L hyA))) htx
  have hyz : y⁻¹ * x ∈ zpowers d.t := by
    rw [← hd.sec3_1'.1]
    exact Subgroup.mem_inf.2 ⟨hyx, hyxt⟩
  rw [show x = y * (y⁻¹ * x) by group]
  exact mul_mem (d.A₃_le_B₃ hyA) (mem_sup_left hyz)

theorem Hyp.isPGroup_B₃ (hd : d.Hyp) : IsPGroup 2 d.B₃ := by
  rw [← hd.R_eq_B₃ (involutionsConjIntoV h) (outerInvolutionFusion h) (perfectLeInn h)
    (twoCentralizerV h)]
  exact hd.isPGroup_T.to_le inf_le_left

theorem Hyp.B₃_le_centralizer_B₁ (hd : d.Hyp) : d.B₃ ≤ centralizer (d.B₁ : Set G) :=
  fun b hb => mem_centralizer_iff.2 fun y hy => hd.B₁_commute_B₃ y hy b hb

theorem Hyp.normalizer_B₁_le (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ≤ normalizer (d.B₃ : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun b hb => ?_
  obtain ⟨k, hk⟩ := hd.isPGroup_B₃ ⟨b, hb⟩
  have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine hd.mem_B₃_of_pow ?_ (k := k) ?_
  · exact (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.B₁ hg) b).1
      (hd.B₃_le_centralizer_B₁ hb)
  · rw [conj_pow, hbk, mul_one, mul_inv_cancel]

theorem Hyp.normalizer_B₁_eq (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) = normalizer (d.B₃ : Set G) :=
  le_antisymm hd.normalizer_B₁_le hd.normalizer_B₃_le

theorem Hyp.normalizer_B₁_le_normalizer_A₁ (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ≤ normalizer (d.A₁ : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun a ha => ?_
  have := hd.conj_mem_A₁ (inv_mem (hd.normalizer_B₁_le hg)) ha
  rwa [inv_inv] at this

theorem Hyp.cosetData_B₁ (hd : d.Hyp) : CosetData (normalizer (d.B₁ : Set G)) d.A₁ d.t :=
  CosetData.of_le_normalizer hd.t_mul_t
    (((d.A₁_le_A₃.trans d.A₃_le_P).trans d.P_le_L).trans hd.L_le_centralizer)
    d.isElementaryAbelian_A₁ hd.normalizer_B₁_le_normalizer_A₁ (by rw [sup_comm]; exact le_rfl)

theorem Hyp.eq_bot_or_eq_A₁ (hd : d.Hyp) {W : Subgroup G} (hW : W ≤ d.A₁)
    (hWn : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det),
      d.η (lev (hK := h) A hA) ∈ normalizer (W : Set G)) : W = ⊥ ∨ W = d.A₁ := by
  set W₀ : Subgroup (hypSU h 2 1) := W.comap d.η ⊓ Vsub h with hW₀
  have hW₀V : W₀ ≤ Vsub h := inf_le_right
  have hmap : d.pull W₀ = W := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hv.1
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := hW hw
      exact ⟨v, ⟨hw, hv⟩, rfl⟩
  have hcard : Nat.card W = Nat.card W₀ := by
    rw [← hmap]
    exact d.card_pull (hW₀V.trans (Vsub_le_Ssub.trans Ssub_le_Usub))
  set X : Set (hypSU h 2 1) := (W₀ : Set (hypSU h 2 1)) \ {1} with hX
  have hXsub : X ⊆ (Vsub h : Set (hypSU h 2 1)) \ {1} := Set.sdiff_subset_sdiff_left hW₀V
  have hXinv : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ v ∈ X,
      lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ ∈ X := by
    intro A hA v hv
    obtain ⟨⟨hvW, hvV⟩, hv1⟩ := hv
    refine ⟨⟨?_, lev_conj_mem_Vsub A hA hvV⟩, fun h1 => hv1 ?_⟩
    · change d.η _ ∈ W
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (hWn A hA) _).1 hvW
    · have h1' : lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ = 1 := h1
      change v = 1
      calc v = (lev (hK := h) A hA)⁻¹ * (lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹) *
            lev (hK := h) A hA := by group
        _ = 1 := by rw [h1']; group
  have hXcard := leviOrbitsV h hd.two_le hd.center_hypPSU X hXsub hXinv
  have hXW : Nat.card X = Nat.card W₀ - 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (one_mem W₀), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe]
  have hdvd : Nat.card W₀ ∣ 2 ^ (f * 4) := by
    have := Subgroup.card_dvd_of_le hW₀V
    rwa [card_Vsub, ← pow_mul] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hpos : 0 < Nat.card W₀ := Nat.card_pos
  rcases hXcard with h0 | h1 | h2 | h3
  · left
    rw [← Subgroup.card_eq_one, hcard]
    omega
  · exact absurd (by rw [← hm]; omega) (two_pow_ne_orbit hd.two_le).1
  · exact absurd (by rw [← hm]; omega) (two_pow_ne_orbit hd.two_le).2
  · right
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    rw [d.card_A₁, hcard]
    have : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem Hyp.η_lev_mem (hd : d.Hyp) (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    d.η (lev (hK := h) A hA) ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) := by
  have ht : d.η (lev (hK := h) A hA) ∈ centralizer ({d.t} : Set G) :=
    hd.L_le_centralizer (d.η_mem _)
  refine ⟨?_, ht⟩
  have hA₁ : d.η (lev (hK := h) A hA) ∈ normalizer (d.A₁ : Set G) :=
    mem_normalizer_of_conj_le fun a ha => by
      obtain ⟨v, hv, rfl⟩ := ha
      exact ⟨_, lev_conj_mem_Vsub A hA hv, by rw [map_mul, map_mul, map_inv]⟩
  exact mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers ht)) hA₁

theorem Hyp.A₁_ne_bot (hd : d.Hyp) : d.A₁ ≠ ⊥ := fun e => by
  have h1 := d.card_A₁
  rw [e, Subgroup.card_bot] at h1
  have h4 := hd.four_le
  have : 4 ≤ (2 ^ f) ^ 4 :=
    h4.trans (Nat.le_self_pow (by norm_num) _)
  omega

theorem Hyp.le_B₃_of_normal (hd : d.Hyp) {R : Subgroup G}
    (hR : R ≤ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G))
    (hRn : normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) ≤ normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) : R ≤ d.B₃ := by
  have hA₁2 : IsPGroup 2 d.A₁ := d.isPGroup_P.to_le (d.A₁_le_A₃.trans d.A₃_le_P)
  have hRA : R ≤ normalizer (d.A₁ : Set G) := fun r hr =>
    hd.normalizer_B₁_le_normalizer_A₁ (hR hr).1
  have hW := Prelim.inf_centralizer_ne_bot_of_pow_mem hA₁2 hd.A₁_ne_bot hRA fun y hy => by
    obtain ⟨k, hk⟩ := hR2 ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  rcases hd.eq_bot_or_eq_A₁ inf_le_left (fun A hA => mem_normalizer_inf
    (hd.normalizer_B₁_le_normalizer_A₁ (hd.η_lev_mem A hA).1)
    (Prelim.normalizer_le_normalizer_centralizer R (hRn (hd.η_lev_mem A hA)))) with h0 | h1
  · exact absurd h0 hW
  · have hRA₁ : R ≤ centralizer (d.A₁ : Set G) := fun r hr =>
      mem_centralizer_iff.2 fun a ha => by
        have ha' : a ∈ d.A₁ ⊓ centralizer (R : Set G) := by rw [h1]; exact ha
        exact (mem_centralizer_iff.1 ha'.2 r hr).symm
    intro r hr
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    exact hd.mem_B₃_of_pow (mem_centralizer_sup (mem_centralizer_zpowers (hR hr).2) (hRA₁ hr))
      (k := k) (by simpa using congrArg Subtype.val hk)

theorem Hyp.V_le_centralizer_A₁ (hd : d.Hyp) : d.V ≤ centralizer (d.A₁ : Set G) := fun _ hv =>
  Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (d.A₁_le_A₃.trans d.A₃_le_P))
    (hd.CB₄I₃_le_centralizer_P (hd.V_le_CB₄I₃ hv))

theorem Hyp.V_le_normalizer_B₁ (hd : d.Hyp) : d.V ≤ normalizer (d.B₁ : Set G) := by
  intro v hv
  have hvB : v ∈ d.B₄ := (hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hv
  have hvA := hd.V_le_centralizer_A₁ hv
  have hle : d.B₁ ≤ d.B₁.comap (MulAut.conj v).toMonoidHom := by
    refine sup_le (zpowers_le.2 ?_) fun a ha => ?_
    · change v * d.t * v⁻¹ ∈ d.B₁
      have hz := hd.cr_mem (inv_mem hvB)
      rw [inv_inv] at hz
      have e : v * d.t * v⁻¹ = (v * d.t * v⁻¹ * d.t) * d.t := by
        rw [mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
      rw [e]
      exact mul_mem (mem_sup_right (d.Zp_le_A₁ hz)) (mem_sup_left (mem_zpowers _))
    · change v * a * v⁻¹ ∈ d.B₁
      rw [(mem_centralizer_iff.1 hvA a ha).symm, mul_inv_cancel_right]
      exact mem_sup_right ha
  exact mem_normalizer_of_conj_le fun b hb => hle hb

theorem Hyp.V_comm_mem_B₃ (hd : d.Hyp) {v k : G} (hv : v ∈ d.V)
    (hk : k ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) ⊓
      centralizer ({d.t} : Set G)) :
    v * k * v⁻¹ * k⁻¹ ∈ d.B₃ := by
  have hvB₄ : v ∈ d.B₄ := (hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hv
  have hkZ : k ∈ centralizer (d.Zp : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 d.Zp_le_A₁) hk.1.2
  have hkN : k ∈ normalizer (d.ZtP : Set G) := by
    rw [hd.ZtP_eq]
    exact Subgroup.centralizer_le_normalizer _
      (mem_centralizer_sup (mem_centralizer_zpowers hk.2) hkZ)
  have hB₂ := (hd.two_core_B₄).2.1 v hvB₄ k ⟨⟨hkN, hkZ⟩, hk.2⟩
  have hvA := hd.V_le_centralizer_A₁ hv
  have hc : v * k * v⁻¹ * k⁻¹ ∈ d.T ⊓ centralizer (d.B₁ : Set G) := by
    refine ⟨hd.tP_le_T (hd.B₂_spec.2.1 hB₂), mem_centralizer_sup
      (mem_centralizer_zpowers (hd.tP_le_centralizer (hd.B₂_spec.2.1 hB₂))) ?_⟩
    exact mul_mem (mul_mem (mul_mem hvA hk.1.2) (inv_mem hvA)) (inv_mem hk.1.2)
  rwa [hd.R_eq_B₃ (involutionsConjIntoV h) (outerInvolutionFusion h) (perfectLeInn h)
    (twoCentralizerV h)] at hc

theorem Hyp.transitive_B₁ (hd : d.Hyp) :
    ∀ y ∈ d.A₁, ∃ q ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G),
      (∀ k ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) ⊓
        centralizer ({d.t} : Set G), q * k * q⁻¹ * k⁻¹ ∈ d.B₃) ∧
        q⁻¹ * d.t * q = d.t * y := by
  have hc := hd.cosetData_B₁
  set H := normalizer (d.B₁ : Set G) with hH
  set K₀ := H ⊓ centralizer (d.A₁ : Set G) ⊓ centralizer ({d.t} : Set G) with hK₀
  have hBn' : ∀ g ∈ H, ∀ b ∈ d.B₃, g * b * g⁻¹ ∈ d.B₃ := fun g hg b hb =>
    (mem_normalizer_iff.1 (hd.normalizer_B₁_le hg) b).1 hb
  have hK : ∀ g ∈ H, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ := fun g hg k hk => hc.conj_mem_kernel hg hk
  set Q : Subgroup G := (H ⊓ centralizer (d.A₁ : Set G)) ⊓ centralizerMod H K₀ d.B₃ hK hBn'
    with hQ
  have hQY : Q ≤ centralizer (d.A₁ : Set G) := fun q hq => hq.1.2
  set φ := crossedHom hd.t_mul_t d.A₁ Q hQY (fun q hq => hc.crossed_mem q hq.1.1) with hφ
  set W : Subgroup G := φ.range.map d.A₁.subtype with hW
  have hWA : W ≤ d.A₁ := map_subtype_le _
  have hmemW : ∀ q (hq : q ∈ Q), q⁻¹ * d.t * q * d.t ∈ W := fun q hq =>
    ⟨φ ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
  have hWmem : ∀ w ∈ W, ∃ q ∈ Q, q⁻¹ * d.t * q * d.t = w := by
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, q.2, rfl⟩
  have hVQ : d.V ≤ Q := fun v hv => ⟨⟨hd.V_le_normalizer_B₁ hv, hd.V_le_centralizer_A₁ hv⟩,
    hd.V_le_normalizer_B₁ hv, fun k hk => hd.V_comm_mem_B₃ hv hk⟩
  have hZW : d.Zp ≤ W := fun z hz => by
    obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq hz
    rw [← hvt]
    exact hmemW v (hVQ hv)
  have hWn : ∀ c ∈ H ⊓ centralizer ({d.t} : Set G), c ∈ normalizer (W : Set G) := fun c hc' => by
    refine mem_normalizer_of_conj_le fun w hw => ?_
    obtain ⟨q, hq, rfl⟩ := hWmem w hw
    have hcq : c * q * c⁻¹ ∈ Q :=
      ⟨hc.conj_mem_inf_centralizer hc'.1 hq.1, conj_mem_centralizerMod hc'.1 hq.2⟩
    have := hmemW _ hcq
    rwa [crossed_conj (mem_centralizer_singleton_iff.1 hc'.2)] at this
  have hWeq : W = d.A₁ := by
    rcases hd.eq_bot_or_eq_A₁ hWA fun A hA => hWn _ (hd.η_lev_mem A hA) with h0 | h1
    · exfalso
      obtain ⟨y, hy, hy1⟩ := hd.exists_mem_Zp_ne_one
      exact hy1 ((Subgroup.mem_bot).1 (h0 ▸ hZW hy))
    · exact h1
  intro y hy
  obtain ⟨q, hq, hqt⟩ := hWmem y (hWeq ▸ hy)
  exact ⟨q, hq.1, hq.2.2, (hc.crossed_eq_iff hy).1 hqt⟩

theorem Hyp.B₃_le_kernel (hd : d.Hyp) :
    d.B₃ ≤ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) ⊓
      centralizer ({d.t} : Set G) := fun _ hb =>
  ⟨⟨Subgroup.centralizer_le_normalizer _ (hd.B₃_le_centralizer_B₁ hb),
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) (hd.B₃_le_centralizer_B₁ hb)⟩,
    hd.B₃_le_centralizer hb⟩

theorem Hyp.two_core_B₅ (hd : d.Hyp) :
    d.B₅ ≤ centralizer (d.A₁ : Set G) ∧
      (∀ x ∈ d.B₅, ∀ k ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) ⊓
        centralizer ({d.t} : Set G), x * k * x⁻¹ * k⁻¹ ∈ d.B₃) ∧
      d.B₅ ⊓ centralizer ({d.t} : Set G) = d.B₃ ∧
      (∀ y ∈ d.A₁, ∃ x ∈ d.B₅, x⁻¹ * d.t * x = d.t * y) ∧
      ∀ g ∈ normalizer (d.B₁ : Set G), ∃ c ∈ normalizer (d.B₁ : Set G) ⊓
        centralizer ({d.t} : Set G), ∃ x ∈ d.B₅, g = c * x := by
  rw [B₅_eq_oTwo]
  exact hd.cosetData_B₁.two_core hd.isPGroup_B₃ hd.B₃_le_kernel hd.normalizer_B₁_le
    (fun R hR hRn hR2 => hd.le_B₃_of_normal hR hRn hR2) hd.transitive_B₁

theorem B₅_le (d : Data G h) : d.B₅ ≤ normalizer (d.B₁ : Set G) := by
  rw [B₅_eq_oTwo]
  exact oTwo_le _

theorem le_normalizer_B₅ (d : Data G h) :
    normalizer (d.B₁ : Set G) ≤ normalizer (d.B₅ : Set G) := by
  rw [B₅_eq_oTwo]
  exact le_normalizer_oTwo _

theorem isPGroup_B₅ (d : Data G h) : IsPGroup 2 d.B₅ := by
  rw [B₅_eq_oTwo]
  exact isPGroup_oTwo _

theorem Hyp.B₃_le_B₅ (hd : d.Hyp) : d.B₃ ≤ d.B₅ := hd.two_core_B₅.2.2.1 ▸ inf_le_left

theorem Hyp.V_le_B₅ (hd : d.Hyp) : d.V ≤ d.B₅ := by
  obtain ⟨hZ, -, -, htr, -⟩ := hd.two_core_B₅
  have hc := hd.cosetData_B₁
  have hB₄2 : IsPGroup 2 d.B₄ := by
    rw [B₄_eq_oTwo]
    exact isPGroup_oTwo _
  have hV2 : IsPGroup 2 d.V := hB₄2.to_le (hd.V_le_CB₄I₃.trans d.CB₄I₃_le)
  have hVB2 : IsPGroup 2 (d.V ⊔ d.B₅ : Subgroup G) := IsPGroup.to_sup_of_normal_right' hV2
    d.isPGroup_B₅ (hd.V_le_normalizer_B₁.trans d.le_normalizer_B₅)
  intro v hv
  have hvH := hd.V_le_normalizer_B₁ hv
  have hz := hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hv)
  obtain ⟨x, hx, hxt⟩ := htr _ (d.Zp_le_A₁ hz)
  have hvt : v⁻¹ * d.t * v = d.t * (v⁻¹ * d.t * v * d.t) := hc.conj_eq_mul hvH
  have hk : v * x⁻¹ ∈ centralizer ({d.t} : Set G) :=
    mul_inv_mem_centralizer_of_conj_eq (hxt.trans hvt.symm)
  have hkA : v * x⁻¹ ∈ centralizer (d.A₁ : Set G) :=
    mul_mem (hd.V_le_centralizer_A₁ hv) (inv_mem (hZ hx))
  obtain ⟨m, hm⟩ := hVB2 ⟨v * x⁻¹, mul_mem (mem_sup_left hv) (inv_mem (mem_sup_right hx))⟩
  have hkB₃ := hd.mem_B₃_of_pow (mem_centralizer_sup (mem_centralizer_zpowers hk) hkA) (k := m)
    (by simpa using congrArg Subtype.val hm)
  rw [show v = (v * x⁻¹) * x by group]
  exact mul_mem (hd.B₃_le_B₅ hkB₃) hx

end Data

end CFSG.LocalAnalysis.EvenBN.U5
