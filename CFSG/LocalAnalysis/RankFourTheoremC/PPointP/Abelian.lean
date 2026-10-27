module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Prop34
import CFSG.LocalAnalysis.RankFourTheoremC.PPointGrun
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAbelianAux
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ComponentClassification Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime]

theorem isMulCommutative_of_isPGroup_p {P : Sylow p G}
    (hPab : IsMulCommutative (P : Subgroup G)) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    IsMulCommutative Q := by
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have h : ((g • P : Sylow p G) : Subgroup G) = (P' : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h
  have hcomm : ∀ a b : G, a ∈ (P' : Subgroup G) → b ∈ (P' : Subgroup G) → a * b = b * a := by
    intro a b ha hb
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hab : a' * b' = b' * a' :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨a', ha'⟩
        ⟨b', hb'⟩)
    show g * a' * g⁻¹ * (g * b' * g⁻¹) = g * b' * g⁻¹ * (g * a' * g⁻¹)
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [hab]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b (hP' a.2) (hP' b.2))

theorem weakClosed_sylow_p {P : Sylow p G} {x : G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (Q : Sylow p G) (hxQ : x ∈ (Q : Subgroup G)) (g : G)
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  have h : ((c • P : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  have hmem : ∀ y ∈ (Q : Subgroup G), c⁻¹ * y * c ∈ (P : Subgroup G) := by
    intro y hy
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    show c⁻¹ * (c * z * c⁻¹) * c ∈ (P : Subgroup G)
    rw [this]
    exact hz
  have h1 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hgz : g * z * g⁻¹ ∈ (Q : Subgroup G) := hg ⟨z, hz, rfl⟩
    have := hmem _ hgz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    simpa [mul_assoc] using this
  have h2 : (zpowers x).map (MulAut.conj c⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (Q : Subgroup G) := zpowers_le.mpr hxQ hz
    have := hmem _ hz'
    simpa [MulAut.conj_apply] using this
  have e1 := hwc _ h1
  have e2 := hwc _ h2
  have e3 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom =
      ((zpowers x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp
  apply Subgroup.map_injective (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).injective
  rw [← e3, e1, e2]

end Generic

theorem commute_of_inner_action_p {X : Type*} [Group X] {p : ℕ} {K R : Subgroup X}
    (hRp : IsPGroup p R) (hKC : ∀ k ∈ K, k ∈ centralizer (K : Set X) → k = 1)
    (hKab : ∀ A : Subgroup X, A ≤ K → IsPGroup p A → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCab : ∀ A : Subgroup X, A ≤ centralizer (K : Set X) → IsPGroup p A →
      ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hinner : ∀ r ∈ R, ∃ k ∈ K, ∀ z ∈ K, r * z * r⁻¹ = k * z * k⁻¹) :
    ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
  set C : Subgroup X := centralizer (K : Set X) with hC
  have hdec : ∀ r ∈ R, ∃ k ∈ K, ∃ c ∈ C, r = k * c := by
    intro r hr
    obtain ⟨k, hk, hkz⟩ := hinner r hr
    refine ⟨k, hk, k⁻¹ * r, ?_, by group⟩
    rw [hC, mem_centralizer_iff]
    intro z hz
    have h := hkz z hz
    calc z * (k⁻¹ * r) = k⁻¹ * (k * z * k⁻¹) * r := by group
      _ = k⁻¹ * (r * z * r⁻¹) * r := by rw [h]
      _ = k⁻¹ * r * z := by group
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    mem_centralizer_iff.mp hc k hk
  have hmul : ∀ k ∈ K, ∀ c ∈ C, ∀ k' ∈ K, ∀ c' ∈ C,
      k * k' * (c * c') = (k * c) * (k' * c') := fun k _ c hc k' hk' c' _ => by
    calc k * k' * (c * c') = k * (k' * c) * c' := by group
      _ = k * (c * k') * c' := by rw [hcomm k' hk' c hc]
      _ = (k * c) * (k' * c') := by group
  have hinv : ∀ k ∈ K, ∀ c ∈ C, k⁻¹ * c⁻¹ = (k * c)⁻¹ := fun k hk c hc => by
    have hcm : Commute k c := hcomm k hk c hc
    rw [mul_inv_rev]
    exact hcm.inv_inv.eq
  let I : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ∃ c ∈ C, k * c ∈ R}
      mul_mem' := by
        rintro k k' ⟨hk, c, hc, hkc⟩ ⟨hk', c', hc', hkc'⟩
        refine ⟨K.mul_mem hk hk', c * c', C.mul_mem hc hc', ?_⟩
        rw [hmul k hk c hc k' hk' c' hc']
        exact R.mul_mem hkc hkc'
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro k ⟨hk, c, hc, hkc⟩
        refine ⟨K.inv_mem hk, c⁻¹, C.inv_mem hc, ?_⟩
        rw [hinv k hk c hc]
        exact R.inv_mem hkc }
  let J : Subgroup X :=
    { carrier := {c | c ∈ C ∧ ∃ k ∈ K, k * c ∈ R}
      mul_mem' := by
        rintro c c' ⟨hc, k, hk, hkc⟩ ⟨hc', k', hk', hkc'⟩
        refine ⟨C.mul_mem hc hc', k * k', K.mul_mem hk hk', ?_⟩
        rw [hmul k hk c hc k' hk' c' hc']
        exact R.mul_mem hkc hkc'
      one_mem' := ⟨C.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro c ⟨hc, k, hk, hkc⟩
        refine ⟨C.inv_mem hc, k⁻¹, K.inv_mem hk, ?_⟩
        rw [hinv k hk c hc]
        exact R.inv_mem hkc }
  have hI : IsPGroup p I := by
    rintro ⟨k, hk, c, hc, hkc⟩
    obtain ⟨m, hm⟩ := hRp ⟨k * c, hkc⟩
    have hm' : (k * c) ^ p ^ m = 1 := congrArg Subtype.val hm
    have hcm : Commute k c := hcomm k hk c hc
    rw [hcm.mul_pow] at hm'
    refine ⟨m, Subtype.ext ?_⟩
    show k ^ p ^ m = 1
    have h1 : k ^ p ^ m = (c ^ p ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
    refine hKC _ (K.pow_mem hk _) ?_
    rw [h1]
    exact C.inv_mem (C.pow_mem hc _)
  have hJ : IsPGroup p J := by
    rintro ⟨c, hc, k, hk, hkc⟩
    obtain ⟨m, hm⟩ := hRp ⟨k * c, hkc⟩
    have hm' : (k * c) ^ p ^ m = 1 := congrArg Subtype.val hm
    have hcm : Commute k c := hcomm k hk c hc
    rw [hcm.mul_pow] at hm'
    refine ⟨m, Subtype.ext ?_⟩
    show c ^ p ^ m = 1
    have h1 : c ^ p ^ m = (k ^ p ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hm'
    have h2 : c ^ p ^ m ∈ K := by
      rw [h1]
      exact K.inv_mem (K.pow_mem hk _)
    exact hKC _ h2 (C.pow_mem hc _)
  intro r hr s hs
  obtain ⟨k, hk, c, hc, rfl⟩ := hdec r hr
  obtain ⟨k', hk', c', hc', rfl⟩ := hdec s hs
  have hkk : k * k' = k' * k :=
    hKab I (fun a ha => ha.1) hI k ⟨hk, c, hc, hr⟩ k' ⟨hk', c', hc', hs⟩
  have hcc : c * c' = c' * c :=
    hCab J (fun a ha => ha.1) hJ c ⟨hc, k, hk, hr⟩ c' ⟨hc', k', hk', hs⟩
  calc k * c * (k' * c') = k * (c * k') * c' := by group
    _ = k * (k' * c) * c' := by rw [hcomm k' hk' c hc]
    _ = (k * k') * (c * c') := by group
    _ = (k' * k) * (c' * c) := by rw [hkk, hcc]
    _ = k' * (k * c') * c := by group
    _ = k' * (c' * k) * c := by rw [hcomm k hk c' hc']
    _ = k' * c' * (k * c) := by group

section Action

variable (p : ℕ) (x : G)

omit [Finite G] in
private theorem normalizer_zpowers_le_normalizer_centralizer :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hCeq : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have := normalizer_le_normalizer_centralizer (zpowers x : Subgroup G)
  rwa [hCeq] at this

private noncomputable def actC :
    normalizer ((zpowers x : Subgroup G) : Set G) →* MulAut (centralizer ({x} : Set G)) :=
  (centralizer ({x} : Set G)).normalizerMonoidHom.comp
    (Subgroup.inclusion (normalizer_zpowers_le_normalizer_centralizer x))

omit [Finite G] in
private theorem actC_coe (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    ((actC x n c : centralizer ({x} : Set G)) : G) = n * c * n⁻¹ := by
  simp [actC, Subgroup.normalizerMonoidHom_apply_apply_coe]

omit [Finite G] in
private theorem map_actC (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    (primeComplementCore (G := centralizer ({x} : Set G)) p).map (actC x n).toMonoidHom =
      primeComplementCore (G := centralizer ({x} : Set G)) p := by
  have hchar : (primeComplementCore (G := centralizer ({x} : Set G)) p).Characteristic :=
    primeComplementCore_characteristic p
  exact (Subgroup.map_equiv_eq_comap_symm (actC x n) _).trans (hchar.fixed (actC x n).symm)

private noncomputable def actX (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    MulAut (RedCent p x) :=
  QuotientGroup.congr (primeComplementCore (G := centralizer ({x} : Set G)) p)
    (primeComplementCore (G := centralizer ({x} : Set G)) p) (actC x n) (map_actC p x n)

omit [Finite G] in
private theorem actX_mk (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    actX p x n (QuotientGroup.mk c) = QuotientGroup.mk (actC x n c) := rfl

private noncomputable def actXHom :
    normalizer ((zpowers x : Subgroup G) : Set G) →* MulAut (RedCent p x) where
  toFun := actX p x
  map_one' := by
    ext q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    rw [actX_mk]
    simp
  map_mul' n m := by
    ext q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [MulAut.mul_apply, actX_mk, map_mul]

end Action

private noncomputable def restrictAut {X : Type*} [Group X] (K : Subgroup X)
    (hK : ∀ σ : MulAut X, K.map σ.toMonoidHom = K) : MulAut X →* MulAut K where
  toFun σ := (σ.subgroupMap K).trans (MulEquiv.subgroupCongr (hK σ))
  map_one' := by
    ext z
    rfl
  map_mul' σ τ := by
    ext z
    rfl

private theorem normal_centralizer_of_normal {X : Type*} [Group X] {K : Subgroup X}
    (hK : K.Normal) : (centralizer (K : Set X)).Normal :=
  ⟨fun c hc y => by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 : (y⁻¹ * k * y) * c = c * (y⁻¹ * k * y) :=
      mem_centralizer_iff.mp hc (y⁻¹ * k * y) (by simpa using hK.conj_mem k hk y⁻¹)
    calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * k := by group⟩

namespace IsPPoint

theorem weaklyClosed_p {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) {P : Sylow p G}
    {M : Subgroup G} {x : G} (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 2 ≤ n) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) :
    ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    PPointP.IsPPoint.le_centralizer_p hp5 h243 h244 hsig hS hD1 hFC hloc h hn hf hd hReq
  intro g hg
  refine PPointP.IsPPoint.eq_zpowers_of_isConj_p hp5 h243 h244 hsig hS hD1 hFC hloc h hn hf hd
    hReq (L := (zpowers x).map (MulAut.conj g).toMonoidHom) (le_inf hg (hg.trans hPC)) ?_
    ⟨g, rfl⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, h.elem.2.1]

theorem isMulCommutative_sylow_p {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) {P : Sylow p G}
    {M : Subgroup G} {x : G} (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 2 ≤ n) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) :
    IsMulCommutative (P : Subgroup G) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨f, W, hfadd, -, -, -, -, -, -, -, ⟨eK⟩, -, hsurj, -, -, -⟩ :=
    PPointP.IsPPoint.exists_borelData_p hp2 hloc h hn hp5 hf hd hReq
  have hxo : orderOf x = p := h.elem.2.1
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    PPointP.IsPPoint.le_centralizer_p hp5 h243 h244 hsig hS hD1 hFC hloc h hn hf hd hReq
  have hxc : ∀ y ∈ (P : Subgroup G), y * x = x * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (hPC hy)
  have hwcP := weaklyClosed_p hp5 h243 h244 hsig hS hD1 hFC hloc h hn hf hd hReq
  have hG : commutator G = ⊤ := by
    have := hS.simple
    have hnormal : (commutator G).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hS.nonab
      apply hab
      have : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h0
  have hgrun := sylow_le_commutator_normalizer_zpowers P hxo h.mem hxc
    (fun Q hxQ g hg => weakClosed_sylow_p hwcP Q hxQ g hg) hG
  have hKn : K.Normal := hf.red.normal
  have hKchar : ∀ σ : MulAut (RedCent p x), K.map σ.toMonoidHom = K := fun σ =>
    hf.red.unique _ ((LocalComponents.equiv_iff σ K).mpr hf.red.component)
  set N : Subgroup G := normalizer ((zpowers x : Subgroup G) : Set G) with hN
  let autK : N →* MulAut K := (restrictAut K hKchar).comp (actXHom p x)
  have hFcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hcard3 : 3 < Nat.card (GaloisField p n) := by
    rw [hFcard]
    calc 3 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (by omega)
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hinner : ∀ r ∈ (R : Subgroup (RedCent p x)), ∃ k ∈ K, ∀ z ∈ K,
      r * z * r⁻¹ = k * z * k⁻¹ := by
    intro r hr
    rw [hReq] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    have hcP : (c : G) ∈ (P : Subgroup G) := (Subgroup.mem_subgroupOf.mp hc).1
    have hcN : (c : G) ∈ N := by
      have : (c : G) ∈ centralizer ({x} : Set G) := c.2
      rw [hN, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      congr 1
      show (c : G) * x * (c : G)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_singleton_iff.mp this
    have hcomm : (c : G) ∈ ⁅N, N⁆ := hgrun hcP
    rw [← map_subtype_commutator] at hcomm
    obtain ⟨ν, hν, hνc⟩ := hcomm
    obtain ⟨k, hk⟩ := exists_conj_of_mem_commutator (GaloisField p n) hpodd (by omega) hFcard
      hcard3 eK autK hν
    refine ⟨k, k.2, fun z hz => ?_⟩
    have h1 := hk ⟨z, hz⟩
    have h2 : ((autK ν ⟨z, hz⟩ : K) : RedCent p x) = (QuotientGroup.mk' _ c) * z *
        (QuotientGroup.mk' _ c)⁻¹ := by
      obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective z
      have hνeq : ν = ⟨(c : G), hcN⟩ := Subtype.ext hνc
      show actX p x ν (QuotientGroup.mk c') = _
      rw [actX_mk, hνeq]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      rw [actC_coe]
      simp
    rw [← h2, h1]
    rfl
  have hCn : (centralizer (K : Set (RedCent p x))).Normal := normal_centralizer_of_normal hKn
  have hKC : ∀ k ∈ K, k ∈ centralizer (K : Set (RedCent p x)) → k = 1 := by
    intro k hk hkc
    have hz : (⟨k, hk⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun m =>
      Subtype.ext (mem_centralizer_iff.mp hkc m m.2)
    have := CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eK
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p n))
    rw [this, mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hRKcomm : ∀ a ∈ (R : Subgroup (RedCent p x)) ⊓ K, ∀ b ∈ (R : Subgroup (RedCent p x)) ⊓ K,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hc, rfl⟩ := hsurj a ha
    obtain ⟨t, hc', rfl⟩ := hsurj b hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show f s * f t = f t * f s
    rw [← hfadd, ← hfadd, add_comm]
  have hTcomm : IsMulCommutative (T : Subgroup K) := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    have ha : ((a : K) : RedCent p x) ∈ (R : Subgroup (RedCent p x)) ⊓ K := by
      rw [← hT]
      exact ⟨a, a.2, rfl⟩
    have hb : ((b : K) : RedCent p x) ∈ (R : Subgroup (RedCent p x)) ⊓ K := by
      rw [← hT]
      exact ⟨b, b.2, rfl⟩
    exact hRKcomm _ ha _ hb
  have hKab : ∀ A : Subgroup (RedCent p x), A ≤ K → IsPGroup p A →
      ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro A hAK hA a ha b hb
    have h1 : IsMulCommutative (A.subgroupOf K) :=
      isMulCommutative_of_isPGroup_p (P := T) hTcomm (hA.comap_subtype)
    have := (IsMulCommutative.is_comm (M := A.subgroupOf K)).comm ⟨⟨a, hAK ha⟩, ha⟩
      ⟨⟨b, hAK hb⟩, hb⟩
    exact congrArg (fun z => ((z.1 : K) : RedCent p x)) this
  obtain ⟨T', hT'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hCn.isSubnormal
  have hcyc : IsCyclic ↥((R : Subgroup (RedCent p x)) ⊓ centralizer (K : Set (RedCent p x))) :=
    hf.red.cyclic
  have hT'comm : IsMulCommutative (T' : Subgroup ↥(centralizer (K : Set (RedCent p x)))) :=
    IsMulCommutative.of_comm fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      have ha : ((a : centralizer (K : Set (RedCent p x))) : RedCent p x) ∈
          (R : Subgroup (RedCent p x)) ⊓ centralizer (K : Set (RedCent p x)) := by
        rw [← hT']
        exact ⟨a, a.2, rfl⟩
      have hb : ((b : centralizer (K : Set (RedCent p x))) : RedCent p x) ∈
          (R : Subgroup (RedCent p x)) ⊓ centralizer (K : Set (RedCent p x)) := by
        rw [← hT']
        exact ⟨b, b.2, rfl⟩
      have := (IsMulCommutative.is_comm (M := ↥((R : Subgroup (RedCent p x)) ⊓
        centralizer (K : Set (RedCent p x))))).comm ⟨_, ha⟩ ⟨_, hb⟩
      have key : ((a : centralizer (K : Set (RedCent p x))) : RedCent p x) *
          ((b : centralizer (K : Set (RedCent p x))) : RedCent p x) =
          ((b : centralizer (K : Set (RedCent p x))) : RedCent p x) *
            ((a : centralizer (K : Set (RedCent p x))) : RedCent p x) := congrArg Subtype.val this
      exact key
  have hCab : ∀ A : Subgroup (RedCent p x), A ≤ centralizer (K : Set (RedCent p x)) →
      IsPGroup p A → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro A hAC hA a ha b hb
    have h1 : IsMulCommutative (A.subgroupOf (centralizer (K : Set (RedCent p x)))) :=
      isMulCommutative_of_isPGroup_p (P := T') hT'comm (hA.comap_subtype)
    have := (IsMulCommutative.is_comm
      (M := A.subgroupOf (centralizer (K : Set (RedCent p x))))).comm ⟨⟨a, hAC ha⟩, ha⟩
      ⟨⟨b, hAC hb⟩, hb⟩
    exact congrArg (fun z => ((z.1 : centralizer (K : Set (RedCent p x))) : RedCent p x)) this
  have hRcomm := commute_of_inner_action_p (K := K) (R := (R : Subgroup (RedCent p x)))
    R.isPGroup' hKC hKab hCab hinner
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup p Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup (primeComplementCore_coprime (G := C) p) hQcp
  refine IsMulCommutative.of_comm fun a b => ?_
  have haQ : (⟨a, hPC a.2⟩ : C) ∈ Qc := mem_subgroupOf.mpr ⟨a.2, hPC a.2⟩
  have hbQ : (⟨b, hPC b.2⟩ : C) ∈ Qc := mem_subgroupOf.mpr ⟨b.2, hPC b.2⟩
  have hρa : QuotientGroup.mk' O ⟨a, hPC a.2⟩ ∈ (R : Subgroup (RedCent p x)) := by
    rw [hReq]
    exact ⟨_, haQ, rfl⟩
  have hρb : QuotientGroup.mk' O ⟨b, hPC b.2⟩ ∈ (R : Subgroup (RedCent p x)) := by
    rw [hReq]
    exact ⟨_, hbQ, rfl⟩
  have hc := hRcomm _ hρa _ hρb
  have hmul : (⟨a, hPC a.2⟩ : C) * ⟨b, hPC b.2⟩ = ⟨b, hPC b.2⟩ * ⟨a, hPC a.2⟩ :=
    hinj _ (Qc.mul_mem haQ hbQ) _ (Qc.mul_mem hbQ haQ) (by rw [map_mul, map_mul]; exact hc)
  have key : (a : G) * b = b * a := congrArg Subtype.val hmul
  exact Subtype.ext key

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
