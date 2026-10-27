module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step9

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G} {p f : ℕ}

theorem finite_mulAut' (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective

section Certified


theorem C3Config.mem_of_barAction_mem_range (hI : C3Inputs) (h : C3Config G z L p f) {x : G}
    (hxN : x ∈ normalizer (L : Set G)) (hxH : x ∈ centralizer ({z} : Set G)) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1)
    (hx : barAction L ⟨x, hxN⟩ ∈ (MulAut.conj : Bar L →* MulAut (Bar L)).range) : x ∈ L := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective w
  have hlN : l ∈ normalizer (L : Set G) := le_normalizer hl
  have h1 : barAction L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : Bar L) :=
    barAction_of_mem L ⟨l, hl⟩ hlN
  have h2 : barAction L ⟨x * l⁻¹, mul_mem hxN (inv_mem hlN)⟩ = 1 := by
    have h3 : (⟨x * l⁻¹, mul_mem hxN (inv_mem hlN)⟩ : ↥(normalizer (L : Set G))) =
        ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹ := rfl
    rw [h3, map_mul, map_inv, ← hw, h1, mul_inv_cancel]
  have hK : x * l⁻¹ ∈ coreActionKernel L :=
    (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)
  have hQ : x * l⁻¹ ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L :=
    mem_inf.mpr ⟨mul_mem hxH (inv_mem (h.hL.1 hl)), hK⟩
  rw [h.Q_eq hI] at hQ
  have hle : (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔
      zpowers z ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L :=
    sup_le_sup_left (zpowers_le.mpr h.hzL) _
  have h4 := mul_mem (hle hQ) (mem_sup_right hl)
  rw [inv_mul_cancel_right] at h4
  have := h.normal hI
  exact mem_of_mem_sup_of_two_pow h.hL.1 h4 hxn

theorem C3Config.exists_V (hI : C3Inputs) (h : C3Config G z L p f) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ V : Subgroup G, V ≤ S ∧ S ⊓ L ≤ V ∧ (∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
      (∀ v ∈ V, ∀ w ∈ V, v ∉ L → w ∉ L → v⁻¹ * w ∈ L) ∧
      (∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ V) ∧
      (∀ v ∈ V, v * v ∈ zpowers z → v ∈ L) ∧
      ((∃ s ∈ S, s ∉ V) → ∃ x ∈ S, x ∉ L ∧ x * x ∈ zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Bar L)) := finite_mulAut' _
  set H := centralizer ({z} : Set G) with hH
  have hLn := h.normal hI
  have hHN : H ≤ normalizer (L : Set G) := (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  set ρ : ↥H →* MulAut (Bar L) := (barAction L).comp (Subgroup.inclusion hHN) with hρ
  have hρapp : ∀ x : ↥H, ρ x = barAction L ⟨x, hHN x.2⟩ := fun x => rfl
  set Inn := (MulAut.conj : Bar L →* MulAut (Bar L)).range with hInn
  set C := (⊤ : Subgroup ↥H).map ρ with hC
  set P := (S.subgroupOf H).map ρ with hP
  have hS2 : ∀ s ∈ S, ∃ n : ℕ, s ^ 2 ^ n = 1 := fun s hs => by
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨s, hs⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hρL : ∀ x : ↥H, (x : G) ∈ L → ρ x ∈ Inn := fun x hx =>
    ⟨QuotientGroup.mk ⟨x, hx⟩, (barAction_of_mem L ⟨x, hx⟩ (hHN x.2)).symm⟩
  have hInnL : ∀ x : ↥H, (x : G) ∈ S → ρ x ∈ Inn → (x : G) ∈ L := fun x hxS hx => by
    obtain ⟨n, hn⟩ := hS2 _ hxS
    exact h.mem_of_barAction_mem_range hI (hHN x.2) x.2 hn hx
  have hρP : ∀ s (hs : s ∈ S), ρ ⟨s, hS.le hs⟩ ∈ P := fun s hs => ⟨⟨s, hS.le hs⟩, hs, rfl⟩
  have hInnC : Inn ≤ C := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨⟨l, h.hL.1 hl⟩, mem_top _, barAction_of_mem L ⟨l, hl⟩ (hHN (h.hL.1 hl))⟩
  have hS' : IsSylowOf 2 (S.subgroupOf H) ⊤ := (isSylowOf_map_subtype_iff H).mp (by
    rwa [subgroupOf_map_subtype, map_subtype_top', inf_eq_left.mpr hS.le])
  have hPC : IsSylowOf 2 P C := IsSylowOf.map ρ hS'
  obtain ⟨W, -, hW2, hW3, hW4, hW5, hW6, hW7⟩ := hI.u4 (Bar L) p f h.hp h.hp2 h.h5 h.hcov C P
    hInnC (isSylowIn_iff_isSylowOf.mpr hPC)
  set V := (W.comap ρ).map H.subtype ⊓ S with hV
  have hmemV : ∀ {s : G} (hs : s ∈ S), s ∈ V ↔ ρ ⟨s, hS.le hs⟩ ∈ W := by
    intro s hs
    constructor
    · intro hsV
      obtain ⟨y, hy, hys⟩ := (mem_inf.mp hsV).1
      have h1 : (⟨s, hS.le hs⟩ : ↥H) = y := Subtype.ext hys.symm
      rw [h1]
      exact hy
    · intro hρs
      exact mem_inf.mpr ⟨⟨⟨s, hS.le hs⟩, hρs, rfl⟩, hs⟩
  have hVS : V ≤ S := inf_le_right
  have hz1 : ∀ hzH : z ∈ H, ρ ⟨z, hzH⟩ = 1 := fun hzH => by
    rw [hρapp]
    exact MonoidHom.mem_ker.mp ((mem_ker_barAction L _).mpr (mem_inf.mp h.mem_Q).2)
  refine ⟨V, hVS, fun s hs => ?_, fun s hs v hv => ?_, fun v hv w hw hvL hwL => ?_, ?_,
    fun v hv hv2 => ?_, ?_⟩
  ·
    obtain ⟨hsS, hsL⟩ := mem_inf.mp hs
    exact (hmemV hsS).mpr (hW2 (mem_inf.mpr ⟨hρP s hsS, hρL _ hsL⟩))
  ·
    have hvS := hVS hv
    have hsvS : s * v * s⁻¹ ∈ S := mul_mem (mul_mem hs hvS) (inv_mem hs)
    refine (hmemV hsvS).mpr ?_
    have h1 : (⟨s * v * s⁻¹, hS.le hsvS⟩ : ↥H) =
        ⟨s, hS.le hs⟩ * ⟨v, hS.le hvS⟩ * (⟨s, hS.le hs⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hW3 _ (hρP s hs) _ ((hmemV hvS).mp hv)
  ·
    have hvS := hVS hv
    have hwS := hVS hw
    have hvwS : v⁻¹ * w ∈ S := mul_mem (inv_mem hvS) hwS
    refine hInnL ⟨v⁻¹ * w, hS.le hvwS⟩ hvwS ?_
    have h1 : (⟨v⁻¹ * w, hS.le hvwS⟩ : ↥H) = (⟨v, hS.le hvS⟩)⁻¹ * ⟨w, hS.le hwS⟩ := rfl
    rw [h1, map_mul, map_inv]
    exact hW4 _ ((hmemV hvS).mp hv) _ ((hmemV hwS).mp hw)
      (fun h2 => hvL (hInnL _ hvS h2)) (fun h2 => hwL (hInnL _ hwS h2))
  ·
    obtain ⟨b, ⟨y, hy, rfl⟩, hb⟩ := hW5
    refine ⟨y, hy, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := hb _ (hρP t ht)
    have hkS : ((y : G) ^ k)⁻¹ * t ∈ S := mul_mem (inv_mem (zpow_mem hy k)) ht
    refine ⟨k, (hmemV hkS).mpr ?_⟩
    have h1 : (⟨((y : G) ^ k)⁻¹ * t, hS.le hkS⟩ : ↥H) = (y ^ k)⁻¹ * ⟨t, hS.le ht⟩ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_inv, map_zpow]
    exact hk
  ·
    have hvS := hVS hv
    refine hInnL ⟨v, hS.le hvS⟩ hvS (hW6 _ ((hmemV hvS).mp hv) ?_)
    have h1 : ρ ⟨v, hS.le hvS⟩ * ρ ⟨v, hS.le hvS⟩ = ρ ⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ :=
      (map_mul ρ _ _).symm
    rw [h1]
    have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
    rcases T23.eq_one_or_eq_of_mem_zpowers hzz hv2 with h2 | h2
    · have h3 : (⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ : ↥H) = 1 := Subtype.ext h2
      rw [h3, map_one]
    · have h3 : (⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ : ↥H) =
          ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h2
      rw [h3, hz1]
  ·
    rintro ⟨s, hs, hsV⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hyInn, hy2⟩ :=
      hW7 ⟨ρ ⟨s, hS.le hs⟩, hρP s hs, fun h1 => hsV ((hmemV hs).mpr h1)⟩
    refine ⟨y, hy, fun h1 => hyInn (hρL y h1), ?_⟩
    rw [← h.inf_Q_eq hI hS]
    have h1 : ρ (y * y) = 1 := by rw [map_mul, hy2]
    rw [hρapp] at h1
    exact mem_inf.mpr ⟨mul_mem hy hy, mem_inf.mpr ⟨(y * y).2,
      (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h1)⟩⟩

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
