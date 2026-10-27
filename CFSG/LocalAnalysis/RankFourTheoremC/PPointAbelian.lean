module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointQK
import CFSG.LocalAnalysis.RankFourTheoremC.PPointGrun
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAbelianAux
import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgameAux
import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp34
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.ComponentClassification Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Action

variable (x : G)

omit [Finite G] in
private theorem normalizer_zpowers_le_normalizer_centralizer' :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hCeq : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have := normalizer_le_normalizer_centralizer (zpowers x : Subgroup G)
  rwa [hCeq] at this

private noncomputable def actC :
    normalizer ((zpowers x : Subgroup G) : Set G) →* MulAut (centralizer ({x} : Set G)) :=
  (centralizer ({x} : Set G)).normalizerMonoidHom.comp
    (Subgroup.inclusion (normalizer_zpowers_le_normalizer_centralizer' x))

omit [Finite G] in
private theorem actC_coe (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    ((actC x n c : centralizer ({x} : Set G)) : G) = n * c * n⁻¹ := by
  simp [actC, Subgroup.normalizerMonoidHom_apply_apply_coe]

omit [Finite G] in
private theorem map_actC (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    (primeComplementCore (G := centralizer ({x} : Set G)) 3).map (actC x n).toMonoidHom =
      primeComplementCore (G := centralizer ({x} : Set G)) 3 := by
  have hchar : (primeComplementCore (G := centralizer ({x} : Set G)) 3).Characteristic :=
    primeComplementCore_characteristic 3
  exact (Subgroup.map_equiv_eq_comap_symm (actC x n) _).trans (hchar.fixed (actC x n).symm)

private noncomputable def actX (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    MulAut (RedCent 3 x) :=
  QuotientGroup.congr (primeComplementCore (G := centralizer ({x} : Set G)) 3)
    (primeComplementCore (G := centralizer ({x} : Set G)) 3) (actC x n) (map_actC x n)

omit [Finite G] in
private theorem actX_mk (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    actX x n (QuotientGroup.mk c) = QuotientGroup.mk (actC x n c) := rfl

private noncomputable def actXHom :
    normalizer ((zpowers x : Subgroup G) : Set G) →* MulAut (RedCent 3 x) where
  toFun := actX x
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

private theorem normal_centralizer_of_normal' {X : Type*} [Group X] {K : Subgroup X}
    (hK : K.Normal) : (centralizer (K : Set X)).Normal :=
  ⟨fun c hc y => by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 : (y⁻¹ * k * y) * c = c * (y⁻¹ * k * y) := by
      have := mem_centralizer_iff.mp hc (y⁻¹ * k * y) (by simpa using hK.conj_mem k hk y⁻¹)
      exact this
    calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * k := by group⟩

theorem BorelData3.conj_mem_QK_of_mem_normalizer {P : Sylow 3 G} {M : Subgroup G} {x : G}
    {n : ℕ} {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W)
    {g : G} (hg : g ∈ normalizer ((zpowers x : Subgroup G) : Set G)) {q : G} (hq : q ∈ hB.QK)
    (hgq : g * q * g⁻¹ ∈ (P : Subgroup G)) : g * q * g⁻¹ ∈ hB.QK := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, hρ, hsurj, -, -, hReq⟩ := hB.reduced
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
  have hKchar : ∀ σ : MulAut (RedCent 3 x), K.map σ.toMonoidHom = K := fun σ =>
    hfacts.red.unique _ ((LocalComponents.equiv_iff σ K).mpr hfacts.red.component)
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup 3 Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup (primeComplementCore_coprime (G := C) 3) hQcp
  have hftC : f t ∈ C := mem_centralizer_singleton_iff.mpr (hB.f_comm t)
  obtain ⟨hc, hρt, -⟩ := hρ t
  set ν : normalizer ((zpowers x : Subgroup G) : Set G) := ⟨g, hg⟩ with hν
  have h1 : actX x ν (QuotientGroup.mk ⟨f t, hftC⟩) = QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) :=
    actX_mk x ν _
  have hcoe : ((actC x ν ⟨f t, hftC⟩ : C) : G) = g * f t * g⁻¹ := actC_coe x ν _
  have hKmem : QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) ∈ K := by
    rw [← h1]
    have : QuotientGroup.mk (⟨f t, hftC⟩ : C) ∈ K := hρt.2
    have h2 : actX x ν (QuotientGroup.mk ⟨f t, hftC⟩) ∈ K.map (actX x ν).toMonoidHom :=
      ⟨_, this, rfl⟩
    rwa [hKchar] at h2
  have hmemQc : (actC x ν ⟨f t, hftC⟩ : C) ∈ Qc := by
    rw [hQc, mem_subgroupOf, hcoe]
    exact ⟨hgq, (actC x ν ⟨f t, hftC⟩).2⟩
  have hRmem : QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) ∈ (R : Subgroup (RedCent 3 x)) := by
    rw [hReq]
    exact ⟨_, hmemQc, rfl⟩
  obtain ⟨s, hcs, hs⟩ := hsurj _ ⟨hRmem, hKmem⟩
  have hsQ : (⟨f s, hcs⟩ : C) ∈ Qc := by
    rw [hQc, mem_subgroupOf]
    exact ⟨(hB.le (hB.f_mem_W s)).1, hcs⟩
  have heq := hinj _ hsQ _ hmemQc hs
  refine hB.mem_QK.mpr ⟨s, ?_⟩
  rw [← hcoe, ← heq]

theorem IsPPoint.weaklyClosed_three {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hin : PPointThreeInputs) (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) :
    ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    h.le_centralizer_three hin hS hD1 hFC hloc
  intro g hg
  refine h.eq_zpowers_of_isConj_three hin hS hD1 hFC hloc (L := (zpowers x).map
    (MulAut.conj g).toMonoidHom) (le_inf hg (hg.trans hPC)) ?_ ⟨g, rfl⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, h.elem.2.1]

theorem IsPPoint.isMulCommutative_sylow_three {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hin : PPointThreeInputs) (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) : IsMulCommutative (P : Subgroup G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨n, f, W, hB⟩ := h.exists_borelData3 hin hS hD1 hFC hloc
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, -, hsurj, -, -, hReq⟩ := hB.reduced
  have hxo : orderOf x = 3 := h.elem.2.1
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    h.le_centralizer_three hin hS hD1 hFC hloc
  have hxc : ∀ y ∈ (P : Subgroup G), y * x = x * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (hPC hy)
  have hwcP := h.weaklyClosed_three hin hS hD1 hFC hloc
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
    (fun Q hxQ g hg => weakClosed_sylow hwcP Q hxQ g hg) hG
  have hKn : K.Normal := hfacts.red.normal
  have hKchar : ∀ σ : MulAut (RedCent 3 x), K.map σ.toMonoidHom = K := fun σ =>
    hfacts.red.unique _ ((LocalComponents.equiv_iff σ K).mpr hfacts.red.component)
  set N : Subgroup G := normalizer ((zpowers x : Subgroup G) : Set G) with hN
  let autK : N →* MulAut K := (restrictAut K hKchar).comp (actXHom x)
  have hFcard : Nat.card (GaloisField 3 n) = 3 ^ n :=
    GaloisField.card 3 n (by have := hB.three_le; omega)
  have hcard3 : 3 < Nat.card (GaloisField 3 n) := by
    rw [hFcard]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := hB.three_le; omega)
  have hinner : ∀ r ∈ (R : Subgroup (RedCent 3 x)), ∃ k ∈ K, ∀ z ∈ K,
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
    obtain ⟨k, hk⟩ := exists_conj_of_mem_commutator (GaloisField 3 n) (by decide) (by
      have := hB.three_le; omega) hFcard hcard3 eK autK hν
    refine ⟨k, k.2, fun z hz => ?_⟩
    have h1 := hk ⟨z, hz⟩
    have h2 : ((autK ν ⟨z, hz⟩ : K) : RedCent 3 x) = (QuotientGroup.mk' _ c) * z *
        (QuotientGroup.mk' _ c)⁻¹ := by
      obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective z
      have hνeq : ν = ⟨(c : G), hcN⟩ := Subtype.ext hνc
      show actX x ν (QuotientGroup.mk c') = _
      rw [actX_mk, hνeq]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      rw [actC_coe]
      simp
    rw [← h2, h1]
    rfl
  have hCn : (centralizer (K : Set (RedCent 3 x))).Normal := normal_centralizer_of_normal' hKn
  have hKC : ∀ k ∈ K, k ∈ centralizer (K : Set (RedCent 3 x)) → k = 1 := by
    intro k hk hkc
    have hz : (⟨k, hk⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun m =>
      Subtype.ext (mem_centralizer_iff.mp hkc m m.2)
    have := CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eK
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 n))
    rw [this, mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hRKcomm : ∀ a ∈ (R : Subgroup (RedCent 3 x)) ⊓ K, ∀ b ∈ (R : Subgroup (RedCent 3 x)) ⊓ K,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hc, rfl⟩ := hsurj a ha
    obtain ⟨t, hc', rfl⟩ := hsurj b hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show f s * f t = f t * f s
    rw [← hB.f_add, ← hB.f_add, add_comm]
  have hTcomm : IsMulCommutative (T : Subgroup K) := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    have ha : ((a : K) : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) ⊓ K := by
      rw [← hT]
      exact ⟨a, a.2, rfl⟩
    have hb : ((b : K) : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) ⊓ K := by
      rw [← hT]
      exact ⟨b, b.2, rfl⟩
    exact hRKcomm _ ha _ hb
  have hKab : ∀ A : Subgroup (RedCent 3 x), A ≤ K → IsPGroup 3 A →
      ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro A hAK hA a ha b hb
    have h1 : IsMulCommutative (A.subgroupOf K) :=
      isMulCommutative_of_isPGroup (P := T) hTcomm (hA.comap_subtype)
    have := (IsMulCommutative.is_comm (M := A.subgroupOf K)).comm ⟨⟨a, hAK ha⟩, ha⟩
      ⟨⟨b, hAK hb⟩, hb⟩
    exact congrArg (fun z => ((z.1 : K) : RedCent 3 x)) this
  obtain ⟨T', hT'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hCn.isSubnormal
  have hcyc : IsCyclic ↥((R : Subgroup (RedCent 3 x)) ⊓ centralizer (K : Set (RedCent 3 x))) :=
    hfacts.red.cyclic
  have hT'comm : IsMulCommutative (T' : Subgroup ↥(centralizer (K : Set (RedCent 3 x)))) :=
    IsMulCommutative.of_comm fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      have ha : ((a : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) ∈
          (R : Subgroup (RedCent 3 x)) ⊓ centralizer (K : Set (RedCent 3 x)) := by
        rw [← hT']
        exact ⟨a, a.2, rfl⟩
      have hb : ((b : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) ∈
          (R : Subgroup (RedCent 3 x)) ⊓ centralizer (K : Set (RedCent 3 x)) := by
        rw [← hT']
        exact ⟨b, b.2, rfl⟩
      have := (IsMulCommutative.is_comm (M := ↥((R : Subgroup (RedCent 3 x)) ⊓
        centralizer (K : Set (RedCent 3 x))))).comm ⟨_, ha⟩ ⟨_, hb⟩
      have key : ((a : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) *
          ((b : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) =
          ((b : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) *
            ((a : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x) := congrArg Subtype.val this
      exact key
  have hCab : ∀ A : Subgroup (RedCent 3 x), A ≤ centralizer (K : Set (RedCent 3 x)) →
      IsPGroup 3 A → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro A hAC hA a ha b hb
    have h1 : IsMulCommutative (A.subgroupOf (centralizer (K : Set (RedCent 3 x)))) :=
      isMulCommutative_of_isPGroup (P := T') hT'comm (hA.comap_subtype)
    have := (IsMulCommutative.is_comm
      (M := A.subgroupOf (centralizer (K : Set (RedCent 3 x))))).comm ⟨⟨a, hAC ha⟩, ha⟩
      ⟨⟨b, hAC hb⟩, hb⟩
    exact congrArg (fun z => ((z.1 : centralizer (K : Set (RedCent 3 x))) : RedCent 3 x)) this
  have hRcomm := commute_of_inner_action (K := K) (R := (R : Subgroup (RedCent 3 x)))
    R.isPGroup' hKC hKab hCab hinner
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup 3 Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup (primeComplementCore_coprime (G := C) 3) hQcp
  refine IsMulCommutative.of_comm fun a b => ?_
  have haQ : (⟨a, hPC a.2⟩ : C) ∈ Qc := mem_subgroupOf.mpr ⟨a.2, hPC a.2⟩
  have hbQ : (⟨b, hPC b.2⟩ : C) ∈ Qc := mem_subgroupOf.mpr ⟨b.2, hPC b.2⟩
  have hρa : QuotientGroup.mk' O ⟨a, hPC a.2⟩ ∈ (R : Subgroup (RedCent 3 x)) := by
    rw [hReq]
    exact ⟨_, haQ, rfl⟩
  have hρb : QuotientGroup.mk' O ⟨b, hPC b.2⟩ ∈ (R : Subgroup (RedCent 3 x)) := by
    rw [hReq]
    exact ⟨_, hbQ, rfl⟩
  have hc := hRcomm _ hρa _ hρb
  have hmul : (⟨a, hPC a.2⟩ : C) * ⟨b, hPC b.2⟩ = ⟨b, hPC b.2⟩ * ⟨a, hPC a.2⟩ :=
    hinj _ (Qc.mul_mem haQ hbQ) _ (Qc.mul_mem hbQ haQ) (by rw [map_mul, map_mul]; exact hc)
  have key : (a : G) * b = b * a := congrArg Subtype.val hmul
  exact Subtype.ext key

end CFSG.LocalAnalysis.RankFourTheoremC
