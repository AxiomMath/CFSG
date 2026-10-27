module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.BorelData
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FusionMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma33

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC

section Transitive

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_centralizer_singleton (x g : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : w ∈ centralizer ({x} : Set G) := hw
    have hw' : x * w = w * x := mem_centralizer_iff.mp hw0 x (Set.mem_singleton x)
    refine mem_centralizer_iff.mpr fun a ha => ?_
    rw [Set.mem_singleton_iff.mp ha]
    show g * x * g⁻¹ * (g * w * g⁻¹) = g * w * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hw']
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  · intro hz
    have hz' : g * x * g⁻¹ * z = z * (g * x * g⁻¹) :=
      mem_centralizer_iff.mp hz _ (Set.mem_singleton _)
    refine ⟨g⁻¹ * z * g, ?_, by show g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩
    refine mem_centralizer_iff.mpr fun a ha => ?_
    rw [Set.mem_singleton_iff.mp ha]
    have : g * (x * (g⁻¹ * z * g)) * g⁻¹ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by
      calc g * (x * (g⁻¹ * z * g)) * g⁻¹ = (g * x * g⁻¹) * z := by group
        _ = z * (g * x * g⁻¹) := hz'
        _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

theorem exists_mem_normalizer_conj {p : ℕ} [Fact p.Prime] {x : G} {Q W : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q (centralizer ({x} : Set G))) (hWQ : W ≤ Q)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW1 : ∀ y ∈ Q, y ^ p = 1 → y ∈ W)
    (hWp : ∀ w ∈ W, w ^ p = 1) (g : G) (hg : g * x * g⁻¹ ∈ W) :
    ∃ m ∈ normalizer (W : Set G), m * x * m⁻¹ = g * x * g⁻¹ := by
  set y : G := g * x * g⁻¹ with hy
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (Q.map (MulAut.conj g).toMonoidHom)
      (centralizer ({y} : Set G)) := by
    have hle : Q.map (MulAut.conj g).toMonoidHom ≤ centralizer ({y} : Set G) := by
      rw [← map_centralizer_singleton]
      exact Subgroup.map_mono hQ.le
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    have hcardC : Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
      rw [← map_centralizer_singleton, Subgroup.card_map_of_injective hinj]
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective hinj, hcardC]
    exact hQ.card_eq
  have hWC : W ≤ centralizer ({y} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hWab w hw y hg)
  obtain ⟨c, hcC, hcW⟩ := exists_conj_le_of_isSylowOf hS' hWC (hQ.isPGroup.to_le hWQ)
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.mp hcC
  have hk : ∀ w ∈ W, (g⁻¹ * c) * w * (g⁻¹ * c)⁻¹ ∈ W := by
    intro w hw
    obtain ⟨q, hq, hqeq⟩ := hcW ⟨w, hw, rfl⟩
    have hqeq' : g * q * g⁻¹ = c * w * c⁻¹ := hqeq
    have hqQ : (g⁻¹ * c) * w * (g⁻¹ * c)⁻¹ = q := by
      have : (g⁻¹ * c) * w * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * w * c⁻¹) * g := by group
      rw [this, ← hqeq']
      group
    rw [hqQ]
    refine hW1 q hq ?_
    have hwp := hWp w hw
    have : q = (g⁻¹ * c) * w * (g⁻¹ * c)⁻¹ := hqQ.symm
    rw [this, conj_pow, hwp]
    group
  let φ : W → W := fun w => ⟨(g⁻¹ * c) * w * (g⁻¹ * c)⁻¹, hk w w.2⟩
  have hφinj : Function.Injective φ := by
    intro u w huw
    have h1 : (g⁻¹ * c) * (u : G) * (g⁻¹ * c)⁻¹ = (g⁻¹ * c) * (w : G) * (g⁻¹ * c)⁻¹ :=
      congrArg Subtype.val huw
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφsurj := Finite.surjective_of_injective hφinj
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨v, hv⟩ := hφsurj ⟨w, hw⟩
      have h1 : (g⁻¹ * c) * (v : G) * (g⁻¹ * c)⁻¹ = w := congrArg Subtype.val hv
      have : (c⁻¹ * g) * w * (c⁻¹ * g)⁻¹ = v := by
        rw [← h1]
        group
      rw [this]
      exact v.2
    · intro hw
      have := hk _ hw
      have e : (g⁻¹ * c) * ((c⁻¹ * g) * w * (c⁻¹ * g)⁻¹) * (g⁻¹ * c)⁻¹ = w := by group
      rwa [e] at this
  · have : c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
    rw [this, ← hy]
    have h2 : c⁻¹ * y * c = y := by
      calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
        _ = c⁻¹ * (c * y) := by rw [hcy]
        _ = y := by group
    exact h2

end Transitive

section PElement

variable {G : Type} [Group G]

theorem commute_of_normalizes_zpowers {p : ℕ} [hp : Fact p.Prime] {x g : G} (hx : orderOf x = p)
    (hg : ∃ j : ℕ, g ^ (p ^ j) = 1) (hmem : g * x * g⁻¹ ∈ zpowers x) : g * x = x * g := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  obtain ⟨j, hj⟩ := hg
  have hpow : ∀ m : ℕ, g ^ m * x * (g ^ m)⁻¹ = x ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g ^ (m + 1) * x * (g ^ (m + 1))⁻¹ = g * (g ^ m * x * (g ^ m)⁻¹) * g⁻¹ := by group
        _ = g * x ^ (k ^ m) * g⁻¹ := by rw [ih]
        _ = (g * x * g⁻¹) ^ (k ^ m) := by rw [conj_zpow]
        _ = (x ^ k) ^ (k ^ m) := by rw [← hk]
        _ = x ^ (k ^ (m + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  have h1 : x ^ (k ^ (p ^ j)) = x := by
    rw [← hpow, hj]
    simp
  have h2 : x ^ (k ^ (p ^ j) - 1) = 1 := by
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ k ^ (p ^ j) - 1 := by
    have h' : (orderOf x : ℤ) ∣ k ^ (p ^ j) - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hx] at h'
  have h4 : (k : ZMod p) ^ (p ^ j) = (k : ZMod p) := ZMod.pow_card_pow _
  have h5 : (k : ZMod p) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ (p ^ j) - 1) p).mpr h3
    push_cast at this
    rw [h4] at this
    exact sub_eq_zero.mp this
  have h6 : (p : ℤ) ∣ k - 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) p).mp
    exact this (by push_cast; rw [h5]; ring)
  have h7 : x ^ k = x := by
    have : x ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; exact h6)
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at this
    exact this
  rw [h7] at hk
  rw [← mul_inv_eq_iff_eq_mul]
  exact hk.symm

end PElement

namespace IsPPoint

variable {G : Type} [Group G] [Finite G]

theorem eq_zpowers_of_isConj_p {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) {P : Sylow p G}
    {M : Subgroup G} {x : G} (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 2 ≤ n) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)))
    {L : Subgroup G} (hLQ : L ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hL : Nat.card L = p)
    (hLc : ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom) : L = zpowers x := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨f, W, hfadd, hfinj, hfx, hfne, hWQ, hW, hW3, htor, -⟩ :=
    IsPPoint.exists_borelData_p hp2 hloc h hn hp5 hf hd hReq
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.elem.2.1] at this
  have hf0 : f 0 = 1 := by
    have h1 := hfadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)
  have hfmem : ∀ t, f t ∈ W := fun t => (hW _).mpr ⟨t, 0, hp.out.pos, by simp⟩
  have hxmem : x ∈ W := (hW x).mpr ⟨0, 1, hp.out.one_lt, by rw [hf0]; simp⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, i, -, rfl⟩ := (hW a).mp ha
    obtain ⟨t, j, -, rfl⟩ := (hW b).mp hb
    have c1 : Commute (f s) (f t) := by
      unfold Commute SemiconjBy
      rw [← hfadd, ← hfadd, add_comm]
    have c2 : Commute (f s) (x ^ j) := (show Commute (f s) x from hfx s).pow_right j
    have c3 : Commute (x ^ i) (f t) := ((show Commute (f t) x from hfx t).pow_right i).symm
    have c4 : Commute (x ^ i) (x ^ j) := Commute.pow_pow_self x i j
    exact (Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)).eq
  have hWp : ∀ w ∈ W, w ^ p = 1 := by
    intro w hw
    obtain ⟨t, i, -, rfl⟩ := (hW w).mp hw
    rw [Commute.mul_pow (show Commute (f t) (x ^ i) from
      (show Commute (f t) x from hfx t).pow_right i), ← pow_natCast_of_add f hfadd p t,
      CharP.cast_eq_zero (GaloisField p n) p, zero_mul, hf0, ← pow_mul, mul_comm, pow_mul, hxp,
      one_pow, one_mul]
  have hfd : FusionData G p n (GaloisField p n) f x W :=
    { two_le := hn
      p_n := Or.inl hp5
      card_F := GaloisField.card p n (by omega)
      x_pow := hxp
      f_add := hfadd
      f_inj := hfinj
      f_comm := hfx
      f_ne := hfne
      f_mem := hfmem
      x_mem := hxmem
      mem_iff := fun y hy => (hW y).mp hy
      torus := htor
      no_plane := fun D hDW hDel hDcard =>
        h.not_exists_conj_lines hp2 h243 h244 hsig hS hD1 hFC hloc (hDW.trans hWQ) hDel hDcard
      trans := fun g hg => exists_mem_normalizer_conj h.sylow hWQ hWab hW3 hWp g hg }
  have hLW : L ≤ W := fun y hy => hW3 y (hLQ hy) (by
    have := pow_card_eq_one' (G := ↥L) (x := (⟨y, hy⟩ : L))
    rw [hL] at this
    exact congrArg Subtype.val this)
  exact hfd.eq_zpowers_of_conj hp2 ⟨hLW, hLc⟩

theorem le_centralizer_p {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) {P : Sylow p G}
    {M : Subgroup G} {x : G} (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 2 ≤ n) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  have hxo : orderOf x = p := h.elem.2.1
  have hxQ : x ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hQP : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ (P : Subgroup G) := inf_le_left
  have hPQ := eq_of_isPGroup_of_le_of_normalizer P.isPGroup' hQP (fun g hgP hgN => by
    refine ⟨hgP, ?_⟩
    set L : Subgroup G := (zpowers x).map (MulAut.conj g).toMonoidHom with hL
    have hLQ : L ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzQ : z ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := zpowers_le.mpr hxQ hz
      exact (mem_normalizer_iff.mp hgN z).mp hzQ
    have hLcard : Nat.card L = p := by
      rw [hL, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hxo]
    have hLx := IsPPoint.eq_zpowers_of_isConj_p hp5 h243 h244 hsig hS hD1 hFC hloc h hn hf hd hReq
      hLQ hLcard ⟨g, rfl⟩
    have hmem : g * x * g⁻¹ ∈ zpowers x := by
      rw [← hLx]
      exact ⟨x, mem_zpowers x, rfl⟩
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨g, hgP⟩
    have hgj : g ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
    show g ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact commute_of_normalizes_zpowers hxo ⟨j, hgj⟩ hmem)
  intro g hg
  exact (show g ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) by rw [← hPQ]; exact hg).2

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
