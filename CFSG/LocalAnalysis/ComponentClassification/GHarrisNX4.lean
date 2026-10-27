module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNX3

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

theorem le_normalizer_map_subtype {G : Type} [Group G] {H : Subgroup G} (K : Subgroup ↥H)
    [hK : K.Normal] : H ≤ normalizer (K.map H.subtype : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨n, hn⟩ * l * ⟨n, hn⟩⁻¹, hK.conj_mem l hl _, rfl⟩
  · rintro ⟨l, hl, hlw⟩
    refine ⟨⟨n, hn⟩⁻¹ * l * ⟨n, hn⟩, by simpa using hK.conj_mem l hl ⟨n, hn⟩⁻¹, ?_⟩
    change n⁻¹ * (l : G) * n = w
    rw [show (l : G) = n * w * n⁻¹ from hlw]
    group

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev LG : Subgroup G := D.Lx.map D.Nx.subtype

abbrev PL : Subgroup G := D.X ⊓ D.LG

theorem LG_le_N : D.LG ≤ D.Nx := map_subtype_le _

theorem N_le_normalizer_LG : D.Nx ≤ normalizer (D.LG : Set G) :=
  le_normalizer_map_subtype D.Lx

theorem isSylowOf_P : IsSylowOf 2 D.PL D.LG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact D.isSylowOf_X.inf_of_le_normalizer D.LG_le_N D.N_le_normalizer_LG

theorem mem_Lx_of_mem_LG {w : G} (hw : w ∈ D.LG) : ∃ hN : w ∈ D.Nx, (⟨w, hN⟩ : ↥D.Nx) ∈ D.Lx := by
  obtain ⟨l, hl, rfl⟩ := hw
  exact ⟨l.2, hl⟩

theorem exists_LZX_of_mem_P (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {w : G} (hw : w ∈ D.PL) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ∃ s ∈ SE.LZX, D.toG s = w := by
  obtain ⟨hwX, hwL⟩ := mem_inf.mp hw
  obtain ⟨s, rfl⟩ := D.exists_toG (mem_inf.mp hwX).1
  have hs2 : s * s = 1 := D.toG_injective (by rw [map_mul, hw2, map_one])
  have hs1 : s ≠ 1 := fun h => hw1 (by rw [h, map_one])
  obtain ⟨hN, hL⟩ := D.mem_Lx_of_mem_LG hwL
  exact ⟨s, D.mem_LZX_of_mem_L hP h6 hwX hs2 hs1 hL, rfl⟩

theorem mem_P_of_LZX (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : s ∈ SE.LZX) : D.toG s ∈ D.PL := by
  obtain ⟨hX, hL⟩ := D.mem_L_of_LZX hP h6 hs
  exact mem_inf.mpr ⟨hX, ⟨_, hL, rfl⟩⟩

theorem center_P (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {w : G} (hw : w ∈ D.PL) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwc : ∀ p ∈ D.PL, w * p = p * w) : w = D.z ∨ w = D.t ∨ w = D.t * D.z := by
  obtain ⟨s, hs, rfl⟩ := D.exists_LZX_of_mem_P hP h6 hw hw2 hw1
  have hc : ∀ u ∈ SE.LZX, s * u = u * s := fun u hu => D.toG_injective (by
    rw [map_mul, map_mul]
    exact hwc _ (D.mem_P_of_LZX hP h6 hu))
  rcases SE.center_LZX s hs hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (map_mul _ _ _))


theorem centralizer_le_H_of_mem_P (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {w : G} (hw : w ∈ D.PL) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨s, hs, rfl⟩ := D.exists_LZX_of_mem_P hP h6 hw hw2 hw1
  obtain ⟨⟨c, hc⟩, -⟩ := SE.LZX_spec s hs
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hSH : (D.S : Subgroup G) ≤ normalizer (sigW D.V : Set G) :=
    D.S_le_M.trans (D.M_le_H hC h10 h20)
  have hrep : ∀ r ∈ SE.ZrepsA, centralizer ({D.toG r} : Set G) ≤
      normalizer (sigW D.V : Set G) := by
    intro r hr
    simp only [SE.ZrepsA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inl rfl)
    · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inl rfl))
    · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inr (Or.inl rfl)))
    · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact D.centralizer_repA_le_H hC hidx hxa hA
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact D.centralizer_repA_le_H hC hidx hxa hA
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have e : D.toG s = D.toG c * D.toG (c⁻¹ * s * c) * (D.toG c)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  exact centralizer_le_of_conj (hSH (D.toG_mem c)) (hrep _ hc)

theorem mem_H_of_normalizes_P (hC : GorensteinHaradaThmCInput) (hP : ∀ i < 9,
    D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i)) (h6 : D.FusN 6 5) {n : G}
    (hn : ∀ p ∈ D.PL, n * p * n⁻¹ ∈ D.PL) : n ∈ normalizer (sigW D.V : Set G) := by
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hn' : ∀ p ∈ D.PL, n⁻¹ * p * n ∈ D.PL := by
    have hle : D.PL.map (MulAut.conj n).toMonoidHom ≤ D.PL := by
      rintro _ ⟨p, hp, rfl⟩
      exact hn p hp
    have heq : D.PL.map (MulAut.conj n).toMonoidHom = D.PL := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective])
    intro p hp
    rw [← heq] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    change n⁻¹ * (n * q * n⁻¹) * n ∈ D.PL
    rwa [show n⁻¹ * (n * q * n⁻¹) * n = q by group]
  have hzP : D.z ∈ D.PL := D.mem_P_of_LZX hP h6 (by decide)
  have htP : D.t ∈ D.PL := D.mem_P_of_LZX hP h6 (by decide)
  have hcz : ∀ p ∈ D.PL, D.z * p = p * D.z := fun p hp => by
    have h := D.conj_z_S (mem_inf.mp (mem_inf.mp hp).1).1
    calc D.z * p = p * (p⁻¹ * D.z * p) := by group
      _ = p * D.z := by rw [h]
  have hcen : ∀ w ∈ D.PL, w * w = 1 → w ≠ 1 → (∀ p ∈ D.PL, w * p = p * w) →
      n * w * n⁻¹ = D.z ∨ n * w * n⁻¹ = D.t ∨ n * w * n⁻¹ = D.t * D.z := by
    intro w hw hw2 hw1 hwc
    refine D.center_P hP h6 (hn w hw) (by
      rw [show n * w * n⁻¹ * (n * w * n⁻¹) = n * (w * w) * n⁻¹ by group, hw2]; group)
      (fun h => hw1 (by
        calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group)) fun p hp => ?_
    have h := hwc _ (hn' p hp)
    calc n * w * n⁻¹ * p = n * (w * (n⁻¹ * p * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * p * n) * w) * n⁻¹ := by rw [h]
      _ = p * (n * w * n⁻¹) := by group
  have hMH := D.M_le_H hC h10 h20
  have hk : ∀ w, w = D.z ∨ w = D.t ∨ w = D.t * D.z →
      w ∈ klein D.z D.t D.t_mul_t D.z_comm_t := by
    rintro w (rfl | rfl | rfl)
    · exact mem_klein_left
    · exact mem_klein_right
    · exact mul_mem mem_klein_right mem_klein_left
  have hnB : (n * D.z * n⁻¹ = D.t ∨ n * D.z * n⁻¹ = D.t * D.z) →
      n ∈ normalizer (sigW D.V : Set G) := by
    intro hzt
    have htc : ∀ p ∈ D.PL, D.t * p = p * D.t := by
      intro p hp
      have hc1 : n * D.z * n⁻¹ * p = p * (n * D.z * n⁻¹) := by
        have h' := hcz _ (hn' p hp)
        calc n * D.z * n⁻¹ * p = n * (D.z * (n⁻¹ * p * n)) * n⁻¹ := by group
          _ = n * ((n⁻¹ * p * n) * D.z) * n⁻¹ := by rw [h']
          _ = p * (n * D.z * n⁻¹) := by group
      rcases hzt with h | h <;> rw [h] at hc1
      · exact hc1
      · calc D.t * p = D.t * D.z * (D.z * p) := by
              rw [← mul_assoc, mul_assoc D.t, D.z_mul_z, mul_one]
          _ = D.t * D.z * (p * D.z) := by rw [hcz p hp]
          _ = p * (D.t * D.z) * D.z := by rw [← mul_assoc, hc1]
          _ = p * D.t := by rw [mul_assoc, mul_assoc, D.z_mul_z, mul_one]
    have ht2 := hcen D.t htP D.t_mul_t D.t_ne_one htc
    set B := klein D.z D.t D.t_mul_t D.z_comm_t with hBdef
    have hle : B.map (MulAut.conj n).toMonoidHom ≤ B := by
      rw [map_le_iff_le_comap]
      refine klein_le ?_ ?_
      · change n * D.z * n⁻¹ ∈ B
        exact hk _ (Or.inr hzt)
      · change n * D.t * n⁻¹ ∈ B
        exact hk _ ht2
    have heq : B.map (MulAut.conj n).toMonoidHom = B := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective])
    have hnN : n ∈ normalizer (B : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
      exact heq
    exact D.normalizer_le_H hC h10 h20 (klein_le D.z_mem_V D.t_mem_V)
      (card_klein D.z_mul_z D.z_ne_one D.t_ne_one D.z_ne_t.symm).ge hnN
  rcases hcen D.z hzP D.z_mul_z D.z_ne_one hcz with h | h | h
  · refine hMH (mem_centralizer_singleton_iff.mpr ?_)
    calc n * D.z = n * D.z * n⁻¹ * n := by group
      _ = D.z * n := by rw [h]
  · exact hnB (Or.inl h)
  · exact hnB (Or.inr h)

theorem LG_le_H (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) : D.LG ≤ normalizer (sigW D.V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hSH : (D.S : Subgroup G) ≤ normalizer (sigW D.V : Set G) :=
    D.S_le_M.trans (D.M_le_H hC h10 h20)
  by_contra hne
  set H := normalizer (sigW D.V : Set G) with hHdef
  set H₀ : Subgroup ↥D.LG := H.subgroupOf D.LG with hH₀def
  have hH₀ : H₀ ≠ ⊤ := fun h => hne fun x hx => by
    have hx' : (⟨x, hx⟩ : ↥D.LG) ∈ H₀ := h ▸ mem_top _
    exact mem_subgroupOf.mp hx'
  obtain ⟨P₀, hP₀⟩ := D.isSylowOf_P.exists_sylow_eq_subgroupOf
  have hPH : ∀ p ∈ D.PL, p ∈ H := fun p hp => hSH (mem_inf.mp (mem_inf.mp hp).1).1
  have hP₀H₀ : (P₀ : Subgroup ↥D.LG) ≤ H₀ := by
    rw [hP₀]
    intro p hp
    exact mem_subgroupOf.mpr (hPH _ (mem_subgroupOf.mp hp))
  have hzP : D.z ∈ D.PL := D.mem_P_of_LZX hP h6 (s := SE.gen 0) (by decide)
  have hzL : D.z ∈ D.LG := (mem_inf.mp hzP).2
  have heven : Even (Nat.card H₀) := by
    have hz₀ : (⟨D.z, hzL⟩ : ↥D.LG) ∈ H₀ := mem_subgroupOf.mpr (hPH _ hzP)
    have hord : orderOf (⟨⟨D.z, hzL⟩, hz₀⟩ : H₀) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
  have hCH : ∀ t ∈ H₀, orderOf t = 2 → centralizer ({t} : Set ↥D.LG) ≤ H₀ := by
    intro t ht ht2
    have hSyl : IsSylowOf 2 (P₀ : Subgroup ↥D.LG) H₀ := (isSylowOf_top P₀).of_le hP₀H₀ le_top
    have hz : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
    obtain ⟨c, hcH, hc⟩ := exists_conj_le_of_isSylowOf hSyl (zpowers_le.mpr ht) hz
    have hct := hc t (mem_zpowers t)
    rw [hP₀, mem_subgroupOf] at hct
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have ht1 : t ≠ 1 := fun h => by
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    have hw2 : ((c * t * c⁻¹ : ↥D.LG) : G) * ((c * t * c⁻¹ : ↥D.LG) : G) = 1 := by
      rw [← Subgroup.coe_mul, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt,
        mul_one, mul_inv_cancel]
      rfl
    have hw1 : ((c * t * c⁻¹ : ↥D.LG) : G) ≠ 1 := fun h => ht1 (by
      have h' : c * t * c⁻¹ = 1 := Subtype.ext h
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h']; group)
    have hCw := D.centralizer_le_H_of_mem_P hC hidx hxa hA hP h6 hct hw2 hw1
    have hCw' : centralizer ({c * t * c⁻¹} : Set ↥D.LG) ≤ H₀ := by
      intro v hv
      rw [mem_centralizer_singleton_iff] at hv
      exact mem_subgroupOf.mpr (hCw (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hv)))
    have h := centralizer_le_of_conj (inv_mem hcH) hCw'
    rwa [show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group] at h
  have hN : normalizer ((P₀ : Subgroup ↥D.LG) : Set ↥D.LG) ≤ H₀ := by
    intro n hn
    refine mem_subgroupOf.mpr (D.mem_H_of_normalizes_P hC hP h6 fun p hp => ?_)
    have hpL : p ∈ D.LG := (mem_inf.mp hp).2
    have hp₀ : (⟨p, hpL⟩ : ↥D.LG) ∈ (P₀ : Subgroup ↥D.LG) := by
      rw [hP₀]
      exact mem_subgroupOf.mpr hp
    have h := (mem_normalizer_iff.mp hn _).mp hp₀
    rw [hP₀, mem_subgroupOf] at h
    exact h
  have hSE := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le hH₀ heven hCH P₀ hN
  have hfus : fusionStronglyEmbedded H₀ :=
    ⟨hSE.1, hSE.2.1, fun g hg => hSE.2.2 g⁻¹ fun h => hg (by simpa using inv_mem h)⟩
  obtain ⟨hp₁, hp₂, hne'⟩ := SE.noncomm_LZX
  have hm₁ := D.mem_P_of_LZX hP h6 hp₁
  have hm₂ := D.mem_P_of_LZX hP h6 hp₂
  have hp₁P : (⟨D.toG ⟨4, 0, 0, 0⟩, (mem_inf.mp hm₁).2⟩ : ↥D.LG) ∈ (P₀ : Subgroup ↥D.LG) := by
    rw [hP₀]
    exact mem_subgroupOf.mpr hm₁
  have hp₂P : (⟨D.toG ⟨5, 1, 1, 0⟩, (mem_inf.mp hm₂).2⟩ : ↥D.LG) ∈ (P₀ : Subgroup ↥D.LG) := by
    rw [hP₀]
    exact mem_subgroupOf.mpr hm₂
  have hord : orderOf (⟨D.toG ⟨4, 0, 0, 0⟩, (mem_inf.mp hm₁).2⟩ : ↥D.LG) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two, ← map_mul, SE.LZX_inv _ hp₁, map_one])
      (fun h => absurd (D.toG_eq_one_iff.mp h) (by decide))
  have hcomm := CFSG.StronglyEmbedded.commute_of_mem_sylow_of_fusionStronglyEmbedded hfus P₀
    hp₁P hord hp₂P
  apply hne'
  apply D.toG_injective
  rw [map_mul, map_mul]
  exact (congrArg Subtype.val hcomm.eq).symm

theorem N_le_H_A (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) : centralizer ({D.x} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨hP, ⟨gy, -, hgy⟩, -⟩ := D.fusion_A hC hidx hxa hA
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hSH : (D.S : Subgroup G) ≤ normalizer (sigW D.V : Set G) :=
    D.S_le_M.trans (D.M_le_H hC h10 h20)
  intro n hn
  obtain ⟨l, hl, w, hw, he⟩ := D.mem_L_mul_X hP h6 ⟨n, hn⟩
  have hn' : n = (l : G) * w := he
  rw [hn']
  exact mul_mem (D.LG_le_H hC hidx hxa hA hP h6 ⟨l, hl, rfl⟩) (hSH (mem_inf.mp hw).1)

theorem H_eq_top_A' (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) : normalizer (sigW D.V : Set G) = ⊤ :=
  D.H_eq_top_A hC hidx hxa hA (D.N_le_H_A hC hidx hxa hA)

end GHSylow

end CFSG.ComponentClassification.GHarris
