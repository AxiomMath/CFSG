module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Cl2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Defs

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Notation25.Kplus (N : Notation25 hs) : Subgroup G := N.K ⊔ CFSG.conjugate N.K N.x

@[expose] def Notation25.Mplus (N : Notation25 hs) : Subgroup G :=
  Subgroup.normalizer (N.Kplus : Set G)

end Defs

@[expose] def CaseCFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R → IsL2pType ↥N.K →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))) →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 →
      Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) →
    CFSG.conjugate N.K N.x ≠ N.K →
    (∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) →
    ∀ g : G, g⁻¹ * t * g ∈ N.Mplus → ∃ m ∈ N.Mplus, g⁻¹ * t * g = m⁻¹ * t * m

section Global

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem Lv2520.K_normal_Kplus
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    ∀ w ∈ N.Kplus, ∀ k ∈ N.K, w * k * w⁻¹ ∈ N.K := by
  intro w hw k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (A := N.K) (B := CFSG.conjugate N.K N.x) hcomm hw
  have hbk : b * k = k * b := (hcomm k hk b hb).symm
  have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
    calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
      _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
      _ = a * k * a⁻¹ := by group
  rw [e]
  exact N.K.mul_mem (N.K.mul_mem ha hk) (N.K.inv_mem ha)

theorem Lv2520.Kx_normal_Kplus
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    ∀ w ∈ N.Kplus, ∀ k ∈ CFSG.conjugate N.K N.x, w * k * w⁻¹ ∈ CFSG.conjugate N.K N.x := by
  intro w hw k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (A := N.K) (B := CFSG.conjugate N.K N.x) hcomm hw
  have hak : a * (b * k * b⁻¹) = (b * k * b⁻¹) * a :=
    hcomm a ha _ ((CFSG.conjugate N.K N.x).mul_mem
      ((CFSG.conjugate N.K N.x).mul_mem hb hk) ((CFSG.conjugate N.K N.x).inv_mem hb))
  have e : a * b * k * (a * b)⁻¹ = b * k * b⁻¹ := by
    calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
      _ = (b * k * b⁻¹) * a * a⁻¹ := by rw [hak]
      _ = b * k * b⁻¹ := by group
  rw [e]
  exact (CFSG.conjugate N.K N.x).mul_mem ((CFSG.conjugate N.K N.x).mul_mem hb hk)
    ((CFSG.conjugate N.K N.x).inv_mem hb)

theorem Lv2520.K_le_normalizer_Kx_of_commute
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    N.K ≤ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : k * y * k⁻¹ = y := by rw [hcomm k hk y hy]; group
    rw [this]; exact hy
  · intro hy
    have hw : k⁻¹ * (k * y * k⁻¹) = (k * y * k⁻¹) * k⁻¹ := hcomm k⁻¹ (N.K.inv_mem hk) _ hy
    have : y = k * y * k⁻¹ := by
      calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
        _ = (k * y * k⁻¹) * k⁻¹ * k := by rw [hw]
        _ = k * y * k⁻¹ := by group
    rw [this]; exact hy

theorem Lv2520.eq_K_or_Kx (h : Lv2520 N t zK)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {J : Subgroup G}
    (hJle : J ≤ N.Kplus) (hJn : ∀ z ∈ N.Kplus, ∀ y ∈ J, z * y * z⁻¹ ∈ J)
    (hcard : Nat.card ↥J = Nat.card ↥N.K) : J = N.K ∨ J = CFSG.conjugate N.K N.x := by
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hKplus : N.K ≤ N.Kplus := le_sup_left
  have hnormal : ((J ⊓ N.K).subgroupOf N.K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyK⟩
      exact ⟨hJn k (hKplus hk) y hyJ, N.K.mul_mem (N.K.mul_mem hk hyK) (N.K.inv_mem hk)⟩
    · rintro ⟨hyJ, hyK⟩
      refine ⟨?_, ?_⟩
      · have h1 := hJn k⁻¹ (N.Kplus.inv_mem (hKplus hk)) _ hyJ
        have e : k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y := by group
        rwa [e] at h1
      · have h1 := N.K.mul_mem (N.K.mul_mem (N.K.inv_mem hk) hyK) hk
        have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        rwa [e] at h1
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · right
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hJK : J ⊓ N.K = ⊥ := by
      have := disjoint_iff.mp hbot
      simpa [inf_assoc] using this
    have hcJK : ∀ y ∈ J, ∀ k ∈ N.K, y * k = k * y := by
      intro y hy k hk
      have hc1 : y * k * y⁻¹ * k⁻¹ ∈ N.K :=
        N.K.mul_mem (Lv2520.K_normal_Kplus hcomm y (hJle hy) k hk) (N.K.inv_mem hk)
      have hc2 : y * k * y⁻¹ * k⁻¹ ∈ J := by
        have e : y * k * y⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by group
        rw [e]
        exact J.mul_mem hy (hJn k (hKplus hk) y⁻¹ (J.inv_mem hy))
      have hc : y * k * y⁻¹ * k⁻¹ ∈ J ⊓ N.K := ⟨hc2, hc1⟩
      rw [hJK, Subgroup.mem_bot] at hc
      calc y * k = (y * k * y⁻¹ * k⁻¹) * (k * y) := by group
        _ = k * y := by rw [hc, one_mul]
    have hJKx : J ≤ CFSG.conjugate N.K N.x := by
      intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute (A := N.K)
        (B := CFSG.conjugate N.K N.x) hcomm (hJle hy)
      have haz : a = 1 := by
        refine h.centerless_K a ha (fun k hk => ?_)
        have h1 := hcJK y hy k hk
        rw [← hab] at h1
        have hbk : b * k = k * b := (hcomm k hk b hb).symm
        have h2 : a * k * b = k * a * b := by
          calc a * k * b = a * (k * b) := by group
            _ = a * (b * k) := by rw [hbk]
            _ = a * b * k := by group
            _ = k * (a * b) := h1
            _ = k * a * b := by group
        exact mul_right_cancel h2
      rw [haz, one_mul] at hab
      rw [← hab]
      exact hb
    exact Subgroup.eq_of_le_of_card_ge hJKx (by rw [BenderBranch.card_conjugate]; exact hcard.ge)
  · left
    rw [Subgroup.subgroupOf_eq_top] at htop
    have hKJ : N.K ≤ J := fun k hk => (htop hk).1
    exact (Subgroup.eq_of_le_of_card_ge hKJ hcard.le).symm

theorem Lv2520.x_sq_mem_normalizer (h : Lv2520 N t zK) :
    N.x * N.x ∈ Subgroup.normalizer (N.K : Set G) := by
  have : N.x ^ 2 ∈ N.S := N.x_sq
  rw [pow_two] at this
  exact h.S_le_normalizer this

theorem Lv2520.x_mem_Mplus (h : Lv2520 N t zK)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) : N.x ∈ N.Mplus := by
  have hx2 := h.x_sq_mem_normalizer
  have hx2' : ∀ k ∈ N.K, (N.x * N.x) * k * (N.x * N.x)⁻¹ ∈ N.K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hx2 k).mp hk
  have hx2'' : ∀ k ∈ N.K, (N.x * N.x)⁻¹ * k * (N.x * N.x) ∈ N.K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N.K : Set G)).inv_mem hx2) k).mp hk
    simpa using this
  show N.x ∈ Subgroup.normalizer ((N.Kplus : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (A := N.K)
      (B := CFSG.conjugate N.K N.x) hcomm hy
    have e : N.x * (a * b) * N.x⁻¹ = (N.x * a * N.x⁻¹) * (N.x * b * N.x⁻¹) := by group
    rw [e]
    refine N.Kplus.mul_mem ?_ ?_
    · refine Subgroup.mem_sup_right ?_
      rw [BenderBranch.mem_conjugate_iff]
      have e2 : N.x * (N.x * a * N.x⁻¹) * N.x⁻¹ = (N.x * N.x) * a * (N.x * N.x)⁻¹ := by group
      rw [e2]
      exact hx2' a ha
    · exact Subgroup.mem_sup_left (BenderBranch.mem_conjugate_iff.mp hb)
  · intro hy
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute (A := N.K)
      (B := CFSG.conjugate N.K N.x) hcomm hy
    have e : y = (N.x⁻¹ * a * N.x) * (N.x⁻¹ * b * N.x) := by
      calc y = N.x⁻¹ * (N.x * y * N.x⁻¹) * N.x := by group
        _ = N.x⁻¹ * (a * b) * N.x := by rw [hab]
        _ = (N.x⁻¹ * a * N.x) * (N.x⁻¹ * b * N.x) := by group
    rw [e]
    refine N.Kplus.mul_mem ?_ ?_
    · refine Subgroup.mem_sup_right ?_
      rw [BenderBranch.mem_conjugate_iff]
      have e2 : N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ = a := by group
      rw [e2]; exact ha
    · refine Subgroup.mem_sup_left ?_
      have hb' : N.x * b * N.x⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hb
      have e2 : N.x⁻¹ * b * N.x = (N.x * N.x)⁻¹ * (N.x * b * N.x⁻¹) * (N.x * N.x) := by group
      rw [e2]
      exact hx2'' _ hb'

omit [Finite G] in
theorem mem_normalizer_conjugate_of_aux {K : Subgroup G} {x s : G}
    (h : x * s * x⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    s ∈ Subgroup.normalizer ((CFSG.conjugate K x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp h (x * y * x⁻¹)
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have e : x * (s * y * s⁻¹) * x⁻¹ = (x * s * x⁻¹) * (x * y * x⁻¹) * (x * s * x⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem Lv2520.centralizer_t_le_Mplus (h : Lv2520 N t zK)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k)
    (hp : CaseCParams N t zK R) : Subgroup.centralizer ({t} : Set G) ≤ N.Mplus := by
  have hKN := Lv2520.K_le_normalizer_Kx_of_commute (N := N) hcomm
  have hnorm2 : ∀ g : G, g ∈ Subgroup.normalizer (N.K : Set G) →
      g ∈ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) →
      g ∈ N.Mplus := fun g hg1 hg2 =>
    Subgroup.inf_normalizer_le_normalizer_sup N.K (CFSG.conjugate N.K N.x) ⟨hg1, hg2⟩
  rw [h.concl2518.2.1]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [h.hK0]
    exact fun k hk => hnorm2 k (Subgroup.le_normalizer hk) (hKN hk)
  · intro s hs
    refine hnorm2 s (h.S_le_normalizer hs) (mem_normalizer_conjugate_of_aux ?_)
    exact h.S_le_normalizer ((Subgroup.mem_normalizer_iff.mp N.x_mem.2 s).mp hs)
  · rw [h.hK0]
    intro c hc
    refine hnorm2 c ?_ ?_
    · exact Subgroup.centralizer_le_normalizer _ hc.2
    · refine mem_normalizer_conjugate_of_aux ?_
      have hzK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
      have hcz : c * zK = zK * c := (Subgroup.mem_centralizer_iff.mp hc.2 zK hzK).symm
      apply h.centralizer_t_le_normalizer
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : N.x * c * N.x⁻¹ * t = N.x * (c * zK) * N.x⁻¹ := by
        rw [← hp.htx]; group
      have e2 : t * (N.x * c * N.x⁻¹) = N.x * (zK * c) * N.x⁻¹ := by
        rw [← hp.htx]; group
      rw [e1, e2, hcz]

theorem Lv2520.t_mem_Kx (h : Lv2520 N t zK) (hp : CaseCParams N t zK R) :
    t ∈ CFSG.conjugate N.K N.x := by
  rw [BenderBranch.mem_conjugate_iff]
  have hzK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
  have e : N.x * t * N.x⁻¹ = (N.x * N.x) * zK * (N.x * N.x)⁻¹ := by
    rw [← hp.htx]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp h.x_sq_mem_normalizer zK).mp hzK

theorem Lv2520.involution_conj_t
    (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hfam : OutFamily N.K N.H)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {j : G}
    (hj : j ∈ N.K ∨ j ∈ CFSG.conjugate N.K N.x) (hj1 : j ≠ 1) (hj2 : j * j = 1) :
    ∃ m ∈ N.Mplus, j = m⁻¹ * t * m := by
  have hzK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
  have hxM := h.x_mem_Mplus hcomm
  have hKM : N.K ≤ N.Mplus := fun k hk =>
    Subgroup.le_normalizer (show k ∈ N.Kplus from Subgroup.mem_sup_left hk)
  rcases hj with hjK | hjKx
  · obtain ⟨k, hk, hkj⟩ := outOneClass G N.K N.H N.S (h.outSetting hfam) zK j hzK hjK
      h.facts2511.zK_sq hj2 h.zK_ne_one hj1
    refine ⟨N.x * k⁻¹, N.Mplus.mul_mem hxM (N.Mplus.inv_mem (hKM hk)), ?_⟩
    rw [← hkj, ← hp.htx]
    group
  · have hj' : N.x * j * N.x⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hjKx
    have hj'1 : N.x * j * N.x⁻¹ ≠ 1 := by
      intro h1
      apply hj1
      calc j = N.x⁻¹ * (N.x * j * N.x⁻¹) * N.x := by group
        _ = 1 := by rw [h1]; group
    have hj'2 : (N.x * j * N.x⁻¹) * (N.x * j * N.x⁻¹) = 1 := by
      calc (N.x * j * N.x⁻¹) * (N.x * j * N.x⁻¹) = N.x * (j * j) * N.x⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    obtain ⟨k, hk, hkj⟩ := outOneClass G N.K N.H N.S (h.outSetting hfam) zK (N.x * j * N.x⁻¹) hzK
      hj' h.facts2511.zK_sq hj'2 h.zK_ne_one hj'1
    refine ⟨N.x * k⁻¹ * N.x, N.Mplus.mul_mem (N.Mplus.mul_mem hxM (N.Mplus.inv_mem (hKM hk))) hxM, ?_⟩
    have e : j = N.x⁻¹ * (N.x * j * N.x⁻¹) * N.x := by group
    rw [e, ← hkj, ← hp.htx]
    group

theorem Lv2520.T_inf_K (_h : Lv2520 N t zK) : T ⊓ N.K = N.SK :=
  N.SK_sylow.eq_of_le (le_inf (N.SK_le_S.trans N.S_le_T) N.SK_le_K) inf_le_right
    (hs.setting.isPGroup.to_le inf_le_left)

theorem Lv2520.conjugate_SK_le_S (_h : Lv2520 N t zK) : CFSG.conjugate N.SK N.x ≤ N.S := by
  have hSx : CFSG.conjugate N.S N.x = N.S :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr N.x_mem.2
  calc CFSG.conjugate N.SK N.x ≤ CFSG.conjugate N.S N.x :=
        BenderBranch.conjugate_mono N.SK_le_S N.x
    _ = N.S := hSx

theorem Lv2520.T_inf_Kx (h : Lv2520 N t zK) :
    T ⊓ CFSG.conjugate N.K N.x = CFSG.conjugate N.SK N.x := by
  have hsyl : IsSylowTwoOf (CFSG.conjugate N.SK N.x) (CFSG.conjugate N.K N.x) :=
    N.SK_sylow.map_equiv (MulAut.conj N.x⁻¹)
  exact hsyl.eq_of_le (le_inf (h.conjugate_SK_le_S.trans N.S_le_T)
    (BenderBranch.conjugate_mono N.SK_le_K N.x)) inf_le_right
    (hs.setting.isPGroup.to_le inf_le_left)

theorem Lv2520.conj_K_eq (h : Lv2520 N t zK)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {g : G}
    (hg : g ∈ N.Mplus) :
    CFSG.conjugate N.K g = N.K ∨ CFSG.conjugate N.K g = CFSG.conjugate N.K N.x := by
  refine h.eq_K_or_Kx hcomm (fun y hy => ?_) (fun z hz y hy => ?_) (BenderBranch.card_conjugate _ _)
  · have h1 : g * y * g⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hy
    exact (Subgroup.mem_normalizer_iff.mp hg y).mpr (Subgroup.mem_sup_left h1)
  · have h1 : g * y * g⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hy
    have hz' : g * z * g⁻¹ ∈ N.Kplus := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    rw [BenderBranch.mem_conjugate_iff]
    have e : g * (z * y * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹)⁻¹ := by group
    rw [e]
    exact Lv2520.K_normal_Kplus hcomm _ hz' _ h1

theorem Lv2520.conj_Kx_eq (h : Lv2520 N t zK)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {g : G}
    (hg : g ∈ N.Mplus) :
    CFSG.conjugate (CFSG.conjugate N.K N.x) g = N.K ∨
      CFSG.conjugate (CFSG.conjugate N.K N.x) g = CFSG.conjugate N.K N.x := by
  refine h.eq_K_or_Kx hcomm (fun y hy => ?_) (fun z hz y hy => ?_)
    (by rw [BenderBranch.card_conjugate, BenderBranch.card_conjugate])
  · have h1 : g * y * g⁻¹ ∈ CFSG.conjugate N.K N.x := BenderBranch.mem_conjugate_iff.mp hy
    exact (Subgroup.mem_normalizer_iff.mp hg y).mpr (Subgroup.mem_sup_right h1)
  · have h1 : g * y * g⁻¹ ∈ CFSG.conjugate N.K N.x := BenderBranch.mem_conjugate_iff.mp hy
    have hz' : g * z * g⁻¹ ∈ N.Kplus := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    rw [BenderBranch.mem_conjugate_iff]
    have e : g * (z * y * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹)⁻¹ := by group
    rw [e]
    exact Lv2520.Kx_normal_Kplus hcomm _ hz' _ h1

omit [Finite G] in
theorem two_le_pRank_of_four [Finite G] {A E : Subgroup G} (hEA : E ≤ A) (hE : IsFourSubgroup E) :
    2 ≤ CFSG.Open.pRank 2 A := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E', _, _, hk⟩
    calc k ≤ 2 ^ k := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card E' := hk.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E'
  · exact ⟨E, hEA, hE.1, by rw [hE.2]; norm_num⟩

theorem Lv2520.caseC_global_of_fusion
    (hAsc : Asc75Lemma34Disjoint) (h : Lv2520 N t zK)
    (hfam : OutFamily N.K N.H) (hp : CaseCParams N t zK R)
    (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ N.Mplus → ∃ m ∈ N.Mplus, g⁻¹ * t * g = m⁻¹ * t * m) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := h.facts2511
  have hKx_le : CFSG.conjugate N.K N.x ≤ N.Kplus := le_sup_right
  have hKplusM : N.Kplus ≤ N.Mplus := Subgroup.le_normalizer
  have hKN := Lv2520.K_le_normalizer_Kx_of_commute (N := N) hcomm
  have hinf := h.K_inf_conjugate_eq_bot hKN
  have hfix : ∀ g : G, g⁻¹ * t * g ∈ N.Mplus → g ∈ N.Mplus :=
    unique_fixed_of_fusion (h.centralizer_t_le_Mplus hcomm hp) hfus
  have htM : t ∈ N.Mplus := hKplusM (hKx_le (h.t_mem_Kx hp))
  have htT : t ∈ T := N.S_le_T hf.t_mem_center.1
  have hTM : T ≤ N.Mplus := le_of_unique_fixed_of_isPGroup hs.setting.isPGroup htT htM hfix
  have hfixj : ∀ j : G, (j ∈ N.K ∨ j ∈ CFSG.conjugate N.K N.x) → j ≠ 1 → j * j = 1 →
      ∀ g : G, g⁻¹ * j * g ∈ N.Mplus → g ∈ N.Mplus := by
    intro j hj hj1 hj2 g hg
    obtain ⟨m, hm, hjm⟩ := h.involution_conj_t hp hfam hcomm hj hj1 hj2
    rw [hjm] at hg
    have h1 : (m * g)⁻¹ * t * (m * g) ∈ N.Mplus := by
      have e : (m * g)⁻¹ * t * (m * g) = g⁻¹ * (m⁻¹ * t * m) * g := by group
      rw [e]; exact hg
    have h2 := hfix _ h1
    have e : g = m⁻¹ * (m * g) := by group
    rw [e]
    exact N.Mplus.mul_mem (N.Mplus.inv_mem hm) h2
  have hfixA : ∀ a : G, (a ∈ N.SK ∨ a ∈ CFSG.conjugate N.SK N.x) → a ≠ 1 →
      ∀ g : G, g⁻¹ * a * g ∈ N.Mplus → g ∈ N.Mplus := by
    intro a ha ha1 g hg
    have haS : a ∈ N.S := by
      rcases ha with ha | ha
      · exact N.SK_le_S ha
      · exact h.conjugate_SK_le_S ha
    obtain ⟨n, hn1, hn2⟩ := Tight.exists_involution_pow N.tuple.sylow.isPGroup haS ha1
    have hn : a ^ n ∈ N.K ∨ a ^ n ∈ CFSG.conjugate N.K N.x := by
      rcases ha with ha | ha
      · exact Or.inl (N.K.pow_mem (N.SK_le_K ha) n)
      · exact Or.inr ((CFSG.conjugate N.K N.x).pow_mem
          (BenderBranch.conjugate_mono N.SK_le_K N.x ha) n)
    have hpow : g⁻¹ * a ^ n * g ∈ N.Mplus := by
      have e : g⁻¹ * a ^ n * g = (g⁻¹ * a * g) ^ n := by
        simpa using (conj_pow (a := g⁻¹) (b := a) (i := n)).symm
      rw [e]
      exact N.Mplus.pow_mem hg n
    exact hfixj (a ^ n) hn hn1 (by rw [← pow_two]; exact hn2) g hpow
  have hsc : ∀ a : G, (a ∈ N.SK ∨ a ∈ CFSG.conjugate N.SK N.x) → ∀ g : G, g⁻¹ * a * g ∈ T →
      (g⁻¹ * a * g ∈ N.SK ∨ g⁻¹ * a * g ∈ CFSG.conjugate N.SK N.x) := by
    intro a ha g hg
    by_cases ha1 : a = 1
    · left
      rw [ha1]
      have : g⁻¹ * (1 : G) * g = 1 := by group
      rw [this]
      exact N.SK.one_mem
    have hgM : g ∈ N.Mplus := hfixA a ha ha1 g (hTM hg)
    rcases ha with ha | ha
    · have hb : g⁻¹ * a * g ∈ CFSG.conjugate N.K g := by
        rw [BenderBranch.mem_conjugate_iff]
        have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
        rw [e]; exact N.SK_le_K ha
      rcases h.conj_K_eq hcomm hgM with h1 | h1
      · rw [h1] at hb
        left
        have : g⁻¹ * a * g ∈ T ⊓ N.K := ⟨hg, hb⟩
        rwa [h.T_inf_K] at this
      · rw [h1] at hb
        right
        have : g⁻¹ * a * g ∈ T ⊓ CFSG.conjugate N.K N.x := ⟨hg, hb⟩
        rwa [h.T_inf_Kx] at this
    · have hb : g⁻¹ * a * g ∈ CFSG.conjugate (CFSG.conjugate N.K N.x) g := by
        rw [BenderBranch.mem_conjugate_iff]
        have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
        rw [e]; exact BenderBranch.conjugate_mono N.SK_le_K N.x ha
      rcases h.conj_Kx_eq hcomm hgM with h1 | h1
      · rw [h1] at hb
        left
        have : g⁻¹ * a * g ∈ T ⊓ N.K := ⟨hg, hb⟩
        rwa [h.T_inf_K] at this
      · rw [h1] at hb
        right
        have : g⁻¹ * a * g ∈ T ⊓ CFSG.conjugate N.K N.x := ⟨hg, hb⟩
        rwa [h.T_inf_Kx] at this
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  have hE4x : IsFourSubgroup (CFSG.conjugate E N.x) :=
    ⟨isElemAbelian_conjugate hE4.1 N.x, by rw [BenderBranch.card_conjugate]; exact hE4.2⟩
  have hESKx : CFSG.conjugate E N.x ≤ CFSG.conjugate N.SK N.x :=
    BenderBranch.conjugate_mono hESK N.x
  have hSKbot : N.SK ≠ ⊥ := by
    intro hbot
    have := hE4.2
    have hEbot : E = ⊥ := le_bot_iff.mp (hbot ▸ hESK)
    rw [hEbot, Subgroup.card_bot] at this
    omega
  have hSKxbot : CFSG.conjugate N.SK N.x ≠ ⊥ := by
    intro hbot
    have := hE4x.2
    have hEbot : CFSG.conjugate E N.x = ⊥ := le_bot_iff.mp (hbot ▸ hESKx)
    rw [hEbot, Subgroup.card_bot] at this
    omega
  have hA1T : N.SK ≤ T := N.SK_le_S.trans N.S_le_T
  have hA2T : CFSG.conjugate N.SK N.x ≤ T := h.conjugate_SK_le_S.trans N.S_le_T
  have hAcomm : ∀ a ∈ N.SK, ∀ b ∈ CFSG.conjugate N.SK N.x, a * b = b * a := fun a ha b hb =>
    hcomm a (N.SK_le_K ha) b (BenderBranch.conjugate_mono N.SK_le_K N.x hb)
  have hr1 : 1 < CFSG.Open.pRank 2 N.SK := two_le_pRank_of_four hESK hE4
  have hr2 : 1 < CFSG.Open.pRank 2 (CFSG.conjugate N.SK N.x) := two_le_pRank_of_four hESKx hE4x
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = Subgroup.closure {g : G |
      CFSG.conjugate N.SK g ⊓ N.SK ≠ ⊥ ∨ CFSG.conjugate N.SK g ⊓ CFSG.conjugate N.SK N.x ≠ ⊥ ∨
      CFSG.conjugate (CFSG.conjugate N.SK N.x) g ⊓ N.SK ≠ ⊥ ∨
      CFSG.conjugate (CFSG.conjugate N.SK N.x) g ⊓ CFSG.conjugate N.SK N.x ≠ ⊥} := ⟨_, rfl⟩
  have hkey : ∀ (Ai Aj : Subgroup G), (∀ b ∈ Ai, b ∈ N.SK ∨ b ∈ CFSG.conjugate N.SK N.x) →
      Aj ≤ T → ∀ g : G, CFSG.conjugate Ai g ⊓ Aj ≠ ⊥ → g ∈ N.Mplus := by
    intro Ai Aj hAi hAj g hne'
    obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    have ha₀i : (a₀ : G) ∈ CFSG.conjugate Ai g := a₀.2.1
    have ha₀j : (a₀ : G) ∈ Aj := a₀.2.2
    have hb : g * (a₀ : G) * g⁻¹ ∈ Ai := BenderBranch.mem_conjugate_iff.mp ha₀i
    have hb1 : g * (a₀ : G) * g⁻¹ ≠ 1 := by
      intro h1
      apply ha₀
      apply Subtype.ext
      show (a₀ : G) = 1
      calc (a₀ : G) = g⁻¹ * (g * (a₀ : G) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    refine hfixA _ (hAi _ hb) hb1 g ?_
    have e : g⁻¹ * (g * (a₀ : G) * g⁻¹) * g = a₀ := by group
    rw [e]
    exact hTM (hAj ha₀j)
  have hHM : H ≤ N.Mplus := by
    rw [hHdef]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with hg | hg | hg | hg
    · exact hkey N.SK N.SK (fun b hb => Or.inl hb) hA1T g hg
    · exact hkey N.SK _ (fun b hb => Or.inl hb) hA2T g hg
    · exact hkey _ N.SK (fun b hb => Or.inr hb) hA1T g hg
    · exact hkey _ _ (fun b hb => Or.inr hb) hA2T g hg
  have hsub : (N.SK : Set G) ∪ (CFSG.conjugate N.SK N.x : Set G) ⊆ ↑(H ⊓ T) := by
    intro a ha
    rcases ha with ha | ha
    · refine ⟨?_, hA1T ha⟩
      rw [hHdef]
      refine Subgroup.subset_closure (Or.inl ?_)
      have : CFSG.conjugate N.SK a = N.SK :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ha)
      rw [this, inf_idem]
      exact hSKbot
    · refine ⟨?_, hA2T ha⟩
      rw [hHdef]
      refine Subgroup.subset_closure (Or.inr (Or.inr (Or.inr ?_)))
      have : CFSG.conjugate (CFSG.conjugate N.SK N.x) a = CFSG.conjugate N.SK N.x :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ha)
      rw [this, inf_idem]
      exact hSKxbot
  have hsc' : ∀ a ∈ (N.SK : Set G) ∪ (CFSG.conjugate N.SK N.x : Set G), ∀ g : G,
      g⁻¹ * a * g ∈ T →
      g⁻¹ * a * g ∈ (N.SK : Set G) ∪ (CFSG.conjugate N.SK N.x : Set G) := fun a ha g hg => by
    rcases hsc a ha g hg with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hbotle : N.K ⊓ CFSG.conjugate N.K N.x = ⊥ := hinf
  have hSKinf : N.SK ⊓ CFSG.conjugate N.SK N.x = ⊥ := by
    refine le_bot_iff.mp ?_
    calc N.SK ⊓ CFSG.conjugate N.SK N.x ≤ N.K ⊓ CFSG.conjugate N.K N.x :=
          inf_le_inf N.SK_le_K (BenderBranch.conjugate_mono N.SK_le_K N.x)
      _ = ⊥ := hbotle
  have hres := hAsc G T N.SK (CFSG.conjugate N.SK N.x) H hSKinf hs.setting.sylow hA1T hA2T hAcomm hr1 hr2
    hHdef hsub (fun a ha h' _ hh' => hsc' a ha h' hh')
    (fun a ha g hg => hsc' a ha g hg.1) (fun a ha g hg => hsc' a ha g hg.1)
  rcases hres with htop | ⟨hle, -⟩ | ⟨hle, -⟩ | ⟨-, -, hcard2⟩
  ·
    have hMtop : N.Mplus = ⊤ := top_le_iff.mp (htop ▸ hHM)
    have hKplusN : N.Kplus.Normal := Subgroup.normalizer_eq_top_iff.mp hMtop
    have : IsSimpleGroup G := hs.setting.simple
    have hKbot : N.K ≠ ⊥ := by
      intro hbot
      exact hSKbot (le_bot_iff.mp (hbot ▸ N.SK_le_K))
    rcases hKplusN.eq_bot_or_eq_top with hbot | htopK
    · exact hKbot (le_bot_iff.mp (hbot ▸ (le_sup_left : N.K ≤ N.Kplus)))
    · have hKn : N.K.Normal :=
        ⟨fun k hk g => Lv2520.K_normal_Kplus hcomm g (htopK ▸ Subgroup.mem_top g) k hk⟩
      rcases hKn.eq_bot_or_eq_top with hb | ht
      · exact hKbot hb
      · apply hne
        have hcard : Nat.card ↥(CFSG.conjugate N.K N.x) = Nat.card G := by
          rw [BenderBranch.card_conjugate, ht, Subgroup.card_top]
        rw [Subgroup.card_eq_iff_eq_top] at hcard
        rw [hcard, ht]
  · apply hSKbot
    refine le_bot_iff.mp ?_
    calc N.SK ≤ N.SK ⊓ CFSG.conjugate N.SK N.x := le_inf le_rfl hle
      _ = ⊥ := hSKinf
  · apply hSKxbot
    refine le_bot_iff.mp ?_
    calc CFSG.conjugate N.SK N.x ≤ N.SK ⊓ CFSG.conjugate N.SK N.x := le_inf hle le_rfl
      _ = ⊥ := hSKinf
  · rw [hSKinf, Subgroup.card_bot] at hcard2
    omega

end Global

theorem caseCGlobal_of_fusion
    (hfus : CaseCFusion) : CaseCGlobal := by
  intro hAsc G _ _ T M hs N t zK R h hfam hp hL2p hc1 hc2 hne hcomm
  exact h.caseC_global_of_fusion hAsc hfam hp hne hcomm
    (hfus G T M hs N t zK R h hfam hp hL2p hc1 hc2 hne hcomm)

@[expose] def CaseCOutside : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R → IsL2pType ↥N.K →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))) →
    (∀ i ∈ N.SC, i ≠ 1 → i * i = 1 →
      Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) →
    CFSG.conjugate N.K N.x ≠ N.K →
    (∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) →
    ∀ i ∈ N.Mplus, i * i = 1 → i ∉ N.Kplus → ∀ g : G, g⁻¹ * t * g ≠ i

section FusionFromOutside

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem Lv2520.diag_conj_z
    (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hfam : OutFamily N.K N.H)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {a b : G}
    (ha : a ∈ N.K) (hb : b ∈ CFSG.conjugate N.K N.x) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha2 : a * a = 1) (hb2 : b * b = 1) : ∃ c : G, a * b = c * (t * zK) * c⁻¹ := by
  have hf := h.facts2511
  have hzK : zK ∈ N.K := h.hK0 ▸ hf.zK_mem
  obtain ⟨k, hk, hka⟩ := outOneClass G N.K N.H N.S (h.outSetting hfam) zK a hzK ha hf.zK_sq ha2
    h.zK_ne_one ha1
  have hb' : N.x * b * N.x⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hb
  have hb'1 : N.x * b * N.x⁻¹ ≠ 1 := by
    intro h1
    apply hb1
    calc b = N.x⁻¹ * (N.x * b * N.x⁻¹) * N.x := by group
      _ = 1 := by rw [h1]; group
  have hb'2 : (N.x * b * N.x⁻¹) * (N.x * b * N.x⁻¹) = 1 := by
    calc (N.x * b * N.x⁻¹) * (N.x * b * N.x⁻¹) = N.x * (b * b) * N.x⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  obtain ⟨k₁, hk₁, hk₁b⟩ := outOneClass G N.K N.H N.S (h.outSetting hfam) zK
    (N.x * b * N.x⁻¹) hzK hb' hf.zK_sq hb'2 h.zK_ne_one hb'1
  have hxt : N.x⁻¹ * zK * N.x = t := by
    have hx2 : N.x * N.x ∈ N.S := by
      have := N.x_sq
      rwa [pow_two] at this
    have hc : (N.x * N.x) * t = t * (N.x * N.x) :=
      Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 _ hx2
    calc N.x⁻¹ * zK * N.x = N.x⁻¹ * (N.x⁻¹ * t * N.x) * N.x := by rw [hp.htx]
      _ = (N.x * N.x)⁻¹ * t * (N.x * N.x) := by group
      _ = (N.x * N.x)⁻¹ * (t * (N.x * N.x)) := by group
      _ = (N.x * N.x)⁻¹ * ((N.x * N.x) * t) := by rw [hc]
      _ = t := by group
  have hk'mem : N.x⁻¹ * k₁ * N.x ∈ CFSG.conjugate N.K N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * (N.x⁻¹ * k₁ * N.x) * N.x⁻¹ = k₁ := by group
    rw [this]; exact hk₁
  have hbk : b = (N.x⁻¹ * k₁ * N.x) * t * (N.x⁻¹ * k₁ * N.x)⁻¹ := by
    calc b = N.x⁻¹ * (N.x * b * N.x⁻¹) * N.x := by group
      _ = N.x⁻¹ * (k₁ * zK * k₁⁻¹) * N.x := by rw [hk₁b]
      _ = (N.x⁻¹ * k₁ * N.x) * (N.x⁻¹ * zK * N.x) * (N.x⁻¹ * k₁ * N.x)⁻¹ := by group
      _ = (N.x⁻¹ * k₁ * N.x) * t * (N.x⁻¹ * k₁ * N.x)⁻¹ := by rw [hxt]
  obtain ⟨k', hk'⟩ : ∃ k' : G, k' = N.x⁻¹ * k₁ * N.x := ⟨_, rfl⟩
  rw [← hk'] at hk'mem hbk
  have htKx := h.t_mem_Kx hp
  have hb₀ : k' * t * k'⁻¹ ∈ CFSG.conjugate N.K N.x :=
    (CFSG.conjugate N.K N.x).mul_mem ((CFSG.conjugate N.K N.x).mul_mem hk'mem htKx)
      ((CFSG.conjugate N.K N.x).inv_mem hk'mem)
  have hA : k⁻¹ * (k' * t * k'⁻¹) = (k' * t * k'⁻¹) * k⁻¹ := hcomm k⁻¹ (N.K.inv_mem hk) _ hb₀
  have hB : zK * k' = k' * zK := hcomm zK hzK k' hk'mem
  have hcomm_t : t * zK = zK * t := hf.t_mul_zK
  refine ⟨k * k', ?_⟩
  rw [← hka, hbk, hcomm_t]
  calc k * zK * k⁻¹ * (k' * t * k'⁻¹) = k * zK * (k⁻¹ * (k' * t * k'⁻¹)) := by group
    _ = k * zK * ((k' * t * k'⁻¹) * k⁻¹) := by rw [hA]
    _ = k * ((zK * k') * t * k'⁻¹) * k⁻¹ := by group
    _ = k * ((k' * zK) * t * k'⁻¹) * k⁻¹ := by rw [hB]
    _ = (k * k') * (zK * t) * (k * k')⁻¹ := by group

end FusionFromOutside

theorem caseCFusion_of_outside
    (hout : CaseCOutside) : CaseCFusion := by
  intro G _ _ T M hs N t zK R h hfam hp hL2p hc1 hc2 hne hcomm g hg
  have hf := h.facts2511
  have ht2 : t * t = 1 := hf.t_mul_t
  have hi2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hi1 : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply hf.t_ne_one
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  by_cases hiK : g⁻¹ * t * g ∈ N.Kplus
  · obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute (A := N.K)
      (B := CFSG.conjugate N.K N.x) hcomm hiK
    have hinf := h.K_inf_conjugate_eq_bot (Lv2520.K_le_normalizer_Kx_of_commute (N := N) hcomm)
    have hba : a * b = b * a := hcomm a ha b hb
    have hsq : (a * a) * (b * b) = 1 := by
      calc (a * a) * (b * b) = (a * b) * (a * b) := by
            calc (a * a) * (b * b) = a * (a * b) * b := by group
              _ = a * (b * a) * b := by rw [hba]
              _ = (a * b) * (a * b) := by group
        _ = 1 := by rw [hab]; exact hi2
    have haa : a * a = 1 := by
      have h1 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      have h2 : a * a ∈ N.K ⊓ CFSG.conjugate N.K N.x :=
        ⟨N.K.mul_mem ha ha, h1 ▸ (CFSG.conjugate N.K N.x).inv_mem
          ((CFSG.conjugate N.K N.x).mul_mem hb hb)⟩
      rw [hinf, Subgroup.mem_bot] at h2
      exact h2
    have hbb : b * b = 1 := by
      rw [haa, one_mul] at hsq
      exact hsq
    by_cases ha1 : a = 1
    ·
      rw [ha1, one_mul] at hab
      obtain ⟨m, hm, hjm⟩ := h.involution_conj_t hp hfam hcomm (Or.inr (hab ▸ hb)) hi1 hi2
      exact ⟨m, hm, hjm⟩
    by_cases hb1 : b = 1
    · rw [hb1, mul_one] at hab
      obtain ⟨m, hm, hjm⟩ := h.involution_conj_t hp hfam hcomm (Or.inl (hab ▸ ha)) hi1 hi2
      exact ⟨m, hm, hjm⟩
    ·
      exfalso
      obtain ⟨c, hc⟩ := h.diag_conj_z hp hfam hcomm ha hb ha1 hb1 haa hbb
      rw [hab] at hc
      apply hp.not_conj (g * c)
      calc (g * c)⁻¹ * t * (g * c) = c⁻¹ * (g⁻¹ * t * g) * c := by group
        _ = c⁻¹ * (c * (t * zK) * c⁻¹) * c := by rw [hc]
        _ = t * zK := by group
  · exact absurd rfl (hout G T M hs N t zK R h hfam hp hL2p hc1 hc2 hne hcomm _ hg hi2 hiK g)

end CFSG.QuasithinUnique
