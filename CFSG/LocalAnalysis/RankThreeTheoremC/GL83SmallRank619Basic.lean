module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z : G} {f : ↥K →* GL32}

private theorem Data619.S_le (h : Data619 M B H S K z f) : S ≤ H := h.maxInv.1.1

private theorem Data619.isPGroup_S (h : Data619 M B H S K z f) : IsPGroup 2 S :=
  h.maxInv.1.2.1

private theorem Data619.B_le_normalizer_S (h : Data619 M B H S K z f) :
    B ≤ normalizer (S : Set G) :=
  h.maxInv.1.2.2

private theorem Data619.isPGroup_core (h : Data619 M B H S K z f) : IsPGroup 2 (pCoreOf 2 H) :=
  h.isPGroup_S.to_le h.core_le

private theorem Data619.core_conj_iff (h : Data619 M B H S K z f) {n : G} (hn : n ∈ H) {x : G} :
    x ∈ pCoreOf 2 H ↔ n * x * n⁻¹ ∈ pCoreOf 2 H :=
  mem_normalizer_iff.1 (h.eq_normalizer.le hn) x

private theorem Data619.K_conj_mem (h : Data619 M B H S K z f) {n : G} (hn : n ∈ H) {k : G}
    (hk : k ∈ K) : n * k * n⁻¹ ∈ K :=
  (mem_normalizer_iff.1 (h.K_normal hn) k).1 hk

private theorem Data619.exists_mul_KS (h : Data619 M B H S K z f) {x : G} (hx : x ∈ K ⊔ S) :
    ∃ k ∈ K, ∃ s ∈ S, x = k * s := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K S (h.S_le.trans h.K_normal)] at hx
  obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.1 hx
  exact ⟨k, hk, s, hs, rfl⟩

private def Data619.centK (h : Data619 M B H S K z f) : Subgroup G where
  carrier := {y | y ∈ H ∧ ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H}
  one_mem' := ⟨H.one_mem, fun k _ => by simp⟩
  mul_mem' := by
    rintro y y' ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨H.mul_mem hy hz, fun k hk => ?_⟩
    have e : y * y' * k * (y * y')⁻¹ * k⁻¹ =
        (y * (y' * k * y'⁻¹ * k⁻¹) * y⁻¹) * (y * k * y⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem ((h.core_conj_iff hy).1 (hz' k hk)) (hy' k hk)
  inv_mem' := by
    rintro y ⟨hy, hy'⟩
    refine ⟨H.inv_mem hy, fun k hk => ?_⟩
    have hk' : y⁻¹ * k * y ∈ K := by simpa using h.K_conj_mem (H.inv_mem hy) hk
    have e : y⁻¹ * k * y⁻¹⁻¹ * k⁻¹ = (y * (y⁻¹ * k * y) * y⁻¹ * (y⁻¹ * k * y)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hy' _ hk')

private theorem Data619.centK_le (h : Data619 M B H S K z f) : h.centK ≤ H := fun _ hy => hy.1

private theorem Data619.le_normalizer_centK (h : Data619 M B H S K z f) :
    H ≤ normalizer (h.centK : Set G) := by
  rw [le_normalizer_iff]
  rintro g hg y ⟨hy, hy'⟩
  refine ⟨H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg), fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ K := by simpa using h.K_conj_mem (H.inv_mem hg) hk
  have e : g * y * g⁻¹ * k * (g * y * g⁻¹)⁻¹ * k⁻¹ =
      g * (y * (g⁻¹ * k * g) * y⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (h.core_conj_iff hg).1 (hy' _ hk')

private theorem Data619.core_le_centK (h : Data619 M B H S K z f) : pCoreOf 2 H ≤ h.centK :=
  fun o ho => ⟨h.S_le (h.core_le ho), fun k hk => by
    have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem ho ((h.core_conj_iff (h.K_le hk)).1 (inv_mem ho))⟩

private theorem Data619.centK_K_le (h : Data619 M B H S K z f) {x : G} (hx : x ∈ h.centK)
    (hxK : x ∈ K) : x ∈ pCoreOf 2 H := by
  set c : ↥K := ⟨x, hxK⟩
  have hcen : f c ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := h.f_surj g
    have h1 : f (c * k * c⁻¹ * k⁻¹) = 1 := (h.f_ker _).2 (hx.2 k k.2)
    simp only [map_mul, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  rw [center_GL32, Subgroup.mem_bot] at hcen
  exact (h.f_ker c).1 hcen

private theorem Data619.inv_mul_mem_centK (h : Data619 M B H S K z f) {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : ↥S} {k₀ : ↥K} (hq : MulAut.conj (f k₀) = Φ a) : (k₀ : G)⁻¹ * (a : G) ∈ h.centK := by
  refine ⟨H.mul_mem (H.inv_mem (h.K_le k₀.2)) (h.S_le a.2), fun k hk => ?_⟩
  set κ : ↥K := ⟨k, hk⟩ with hκ
  set κ' : ↥K := ⟨(a : G) * k * (a : G)⁻¹, h.K_conj_mem (h.S_le a.2) hk⟩ with hκ'
  have h1 : f κ' = f k₀ * f κ * (f k₀)⁻¹ := by
    rw [← hΦ a κ κ' rfl, ← hq]
    simp [MulAut.conj_apply]
  have h2 : f (k₀⁻¹ * κ' * k₀ * κ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have h3 := (h.f_ker _).1 h2
  have e : ((k₀⁻¹ * κ' * k₀ * κ⁻¹ : ↥K) : G) =
      (k₀ : G)⁻¹ * (a : G) * k * ((k₀ : G)⁻¹ * (a : G))⁻¹ * k⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hκ, hκ']
    group
  rwa [e] at h3

omit [Finite G] in
private theorem pow_mem_of_pow_eq_one_aux {N T : Subgroup G} (hT : T ≤ normalizer (N : Set G))
    {n t : G} (hn : n ∈ N) (ht : t ∈ T) {m : ℕ} (htm : t ^ m = 1) : (n * t) ^ m ∈ N := by
  have key : ∀ j : ℕ, ∃ n' ∈ N, (n * t) ^ j = n' * t ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (t ^ j * n * (t ^ j)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact le_normalizer_iff.1 hT _ (T.pow_mem ht j) n hn
      · rw [pow_succ, e]
        group
  obtain ⟨n', hn', e⟩ := key m
  rw [e, htm, mul_one]
  exact hn'

private theorem Data619.isPGroup_D (h : Data619 M B H S K z f) :
    IsPGroup 2 ↥(h.centK ⊓ (K ⊔ S)) := by
  rintro ⟨d, hdC, hdKS⟩
  obtain ⟨k, hk, s, hs, rfl⟩ := h.exists_mul_KS hdKS
  obtain ⟨m, hm⟩ := h.isPGroup_S ⟨s, hs⟩
  have hs' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : (k * s) ^ 2 ^ m ∈ K :=
    pow_mem_of_pow_eq_one_aux (h.S_le.trans h.K_normal) hk hs hs'
  have h2 : (k * s) ^ 2 ^ m ∈ h.centK := h.centK.pow_mem hdC _
  obtain ⟨r, hr⟩ := h.isPGroup_core ⟨_, h.centK_K_le h2 h1⟩
  have hr' : ((k * s) ^ 2 ^ m) ^ 2 ^ r = 1 := congrArg Subtype.val hr
  refine ⟨m + r, Subtype.ext ?_⟩
  show (k * s) ^ 2 ^ (m + r) = 1
  rw [pow_add, pow_mul]
  exact hr'

private theorem Data619.core_le_D (h : Data619 M B H S K z f) :
    pCoreOf 2 H ≤ h.centK ⊓ (K ⊔ S) :=
  le_inf h.core_le_centK (h.core_le.trans le_sup_right)

private theorem Data619.mem_normalizer_D (h : Data619 M B H S K z f) {g : G} (hg : g ∈ H)
    (hg' : g ∈ normalizer ((K ⊔ S : Subgroup G) : Set G)) :
    g ∈ normalizer ((h.centK ⊓ (K ⊔ S) : Subgroup G) : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨h.le_normalizer_centK hg, hg'⟩

private theorem Data619.S_le_normalizer_D (h : Data619 M B H S K z f) :
    S ≤ normalizer ((h.centK ⊓ (K ⊔ S) : Subgroup G) : Set G) :=
  fun _ hs => h.mem_normalizer_D (h.S_le hs) ((K ⊔ S).le_normalizer (mem_sup_right hs))

private theorem Data619.K_le_normalizer_D (h : Data619 M B H S K z f) :
    K ≤ normalizer ((h.centK ⊓ (K ⊔ S) : Subgroup G) : Set G) :=
  fun _ hk => h.mem_normalizer_D (h.K_le hk) ((K ⊔ S).le_normalizer (mem_sup_left hk))

private theorem Data619.B_le_normalizer_D (h : Data619 M B H S K z f) :
    B ≤ normalizer ((h.centK ⊓ (K ⊔ S) : Subgroup G) : Set G) :=
  fun _ hb => h.mem_normalizer_D (h.B_le hb)
    (inf_normalizer_le_normalizer_sup K S ⟨h.K_normal (h.B_le hb), h.B_le_normalizer_S hb⟩)

private theorem Data619.D_le_S (h : Data619 M B H S K z f) : h.centK ⊓ (K ⊔ S) ≤ S := by
  have hjoin : IsTwoInvariantIn B H (h.centK ⊓ (K ⊔ S) ⊔ S) :=
    ⟨sup_le (inf_le_left.trans h.centK_le) h.S_le,
      h.isPGroup_D.to_sup_of_normal_left' h.isPGroup_S h.S_le_normalizer_D,
      fun b hb => inf_normalizer_le_normalizer_sup _ _
        ⟨h.B_le_normalizer_D hb, h.B_le_normalizer_S hb⟩⟩
  exact le_sup_left.trans (h.maxInv.2 _ hjoin le_sup_right).le

private theorem Data619.D_le_core (h : Data619 M B H S K z f) :
    h.centK ⊓ (K ⊔ S) ≤ pCoreOf 2 H := by
  by_contra hne
  have hlt : pCoreOf 2 H < h.centK ⊓ (K ⊔ S) :=
    lt_of_le_of_ne h.core_le_D fun e => hne e.ge
  exact h.K_not_le (h.K_le_normalizer_D.trans
    (h.norm_le _ hlt h.D_le_S (sup_le h.S_le_normalizer_D h.B_le_normalizer_D)))

theorem Data619.exists_phi (h : Data619 M B H S K z f) :
    ∃ Φ : ↥S →* MulAut GL32, ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k' := by
  refine exists_inducedHom K S f h.f_surj (h.S_le.trans h.K_normal) ?_
  intro n hn k k' hk'
  rw [h.f_ker, h.f_ker, hk']
  exact h.core_conj_iff (h.S_le hn)

theorem Data619.mem_sup_of_mem_Inn (h : Data619 M B H S K z f) {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : ↥S} (ha : Φ a ∈ L32Insp.Inn) : (a : G) ∈ K ⊔ pCoreOf 2 H := by
  obtain ⟨q, hq⟩ := L32Insp.mem_Inn.1 ha
  obtain ⟨k₀, rfl⟩ := h.f_surj q
  have hy : (k₀ : G)⁻¹ * (a : G) ∈ h.centK ⊓ (K ⊔ S) :=
    ⟨h.inv_mul_mem_centK hΦ hq, mul_mem (mem_sup_left (inv_mem k₀.2)) (mem_sup_right a.2)⟩
  have e : (a : G) = (k₀ : G) * ((k₀ : G)⁻¹ * (a : G)) := by group
  rw [e]
  exact mul_mem (mem_sup_left k₀.2) (mem_sup_right (h.D_le_core hy))

theorem Data619.phi_eq_one_of_mem_core (h : Data619 M B H S K z f) {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : ↥S} (ha : (a : G) ∈ pCoreOf 2 H) : Φ a = 1 := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨k, rfl⟩ := h.f_surj q
  set κ' : ↥K := ⟨(a : G) * k * (a : G)⁻¹, h.K_conj_mem (h.S_le a.2) k.2⟩ with hκ'
  have h1 : f (κ' * k⁻¹) = 1 := by
    refine (h.f_ker _).2 ?_
    have e : ((κ' * k⁻¹ : ↥K) : G) = (a : G) * ((k : G) * (a : G)⁻¹ * (k : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hκ']
      group
    rw [e]
    exact mul_mem ha ((h.core_conj_iff (h.K_le k.2)).1 (inv_mem ha))
  rw [hΦ a k κ' rfl, MulAut.one_apply]
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.1 h1

theorem Data619.exists_mul_of_mem_sup (h : Data619 M B H S K z f) {a : G} (haS : a ∈ S)
    (ha : a ∈ K ⊔ pCoreOf 2 H) : ∃ k ∈ K ⊓ S, ∃ o ∈ pCoreOf 2 H, a = k * o := by
  rw [← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H) (h.K_le.trans h.eq_normalizer.le)] at ha
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 ha
  refine ⟨k, ⟨hk, ?_⟩, o, ho, rfl⟩
  simpa using S.mul_mem haS (S.inv_mem (h.core_le ho))

end CFSG.LocalAnalysis.RankThreeTheoremC
