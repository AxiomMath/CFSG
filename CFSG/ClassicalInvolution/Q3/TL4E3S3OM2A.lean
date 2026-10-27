module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lay
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quot

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

variable {W : Type} [Group W] [Finite W]

theorem oddCoreOf_eq_bot_of_two {X : Subgroup W} (hX : IsPGroup 2 ↥X) : oddCoreOf X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, -⟩ := mem_oddCoreOf_iff.mp hx
  exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) hx
    (hX.to_le (Subgroup.zpowers_le.mpr hxX)))

omit [Finite W] in
theorem inf_eq_bot_of_not_mem {H P : Subgroup W} {z : W} (hz : IsUniqueInvolution H z)
    (hP : IsPGroup 2 ↥P) (hzP : z ∉ P) : H ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxH, hxP⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk'))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
  have hy2 : x ^ (2 ^ m) * x ^ (2 ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hk']
    exact pow_orderOf_eq_one _
  rcases hz.unique _ (H.pow_mem hxH _) hy2 with h1 | h1
  · have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hk'] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  · exact hzP (h1 ▸ P.pow_mem hxP _)

variable {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W} {Q : Type} [Group Q]

omit [Finite W] in
theorem not_mem_ker (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf2 : IsPGroup 2 ↥f.ker) :
    ∀ g : W, g * k * g⁻¹ ∉ f.ker := by
  intro g hg
  apply h.notO2
  refine ⟨f.ker, inferInstance, hf2, ?_⟩
  have := f.normal_ker.conj_mem _ hg g⁻¹
  simpa [mul_assoc] using this

theorem ker_le_center (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf2 : IsPGroup 2 ↥f.ker) :
    f.ker ≤ Subgroup.center W := by
  have hcl := h.fam.hyp.conjInvariant
  have key : ∀ g : W, conjSub g K ≤ Subgroup.centralizer (f.ker : Set W) := by
    intro g
    have hKg : conjSub g K ∈ Φ := hcl g K h.memK
    have hP := inf_eq_bot_of_not_mem (h.invK.conj g) hf2 (not_mem_ker h f hf2 g)
    rw [← h.fam.closure_twoElts hKg, Subgroup.closure_le]
    rintro y ⟨hyK, hy2⟩
    obtain ⟨R, hR, hyR⟩ := IsSylow2In.exists_ge hy2 (Subgroup.zpowers_le.mpr hyK)
    have hRP : R ⊓ f.ker = ⊥ := le_bot_iff.mp ((inf_le_inf_right _ hR.1).trans hP.le)
    have hc := comm613Gen_normal h.fam.hyp (mem_RSet_of_isSylow2In hKg hR) inferInstance hRP
    rw [oddCoreOf_eq_bot_of_two hf2, le_bot_iff] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc (hyR (Subgroup.mem_zpowers y))
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ ⨆ g : W, conjSub g K := by
    rw [h.gen]
    exact Subgroup.mem_top y
  exact (Subgroup.mem_centralizer_iff.mp ((iSup_le key) hy) p hp).symm

theorem center_le_ker [Finite Q] (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker)
    (hQ : PhilipHall.QuaternionBridge.ExLie Q) : Subgroup.center W ≤ f.ker := by
  have hs := Vtx.isSimpleGroup_of_exLie hQ
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨S₀, hS₀, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
      obtain ⟨e⟩ := h.fam.quat K h.memK S₀ hS₀
      have e2 : ↥S₀ ≃* QuaternionGroup 2 := e
      set x : W := (e2.symm (QuaternionGroup.a 1) : W)
      set y : W := (e2.symm (QuaternionGroup.xa 0) : W)
      have hxy : x * y ≠ y * x := by
        intro hc
        have h1 : e2.symm (QuaternionGroup.a 1) * e2.symm (QuaternionGroup.xa 0) =
            e2.symm (QuaternionGroup.xa 0) * e2.symm (QuaternionGroup.a 1) := Subtype.ext hc
        rw [← map_mul, ← map_mul] at h1
        exact absurd (e2.symm.injective h1) (by decide)
      have hP := inf_eq_bot_of_not_mem h.invK hf2 (by simpa using not_mem_ker h f hf2 1)
      have hxK : x ∈ K := hS₀.1 (e2.symm _).2
      have hyK : y ∈ K := hS₀.1 (e2.symm _).2
      have hfxy : f (x * y) = f (y * x) := by
        have hc := Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top (f x)) (f y)
        rw [map_mul, map_mul, hc]
      have hmem : (y * x)⁻¹ * (x * y) ∈ K ⊓ f.ker := by
        refine ⟨K.mul_mem (K.inv_mem (K.mul_mem hyK hxK)) (K.mul_mem hxK hyK), ?_⟩
        show (y * x)⁻¹ * (x * y) ∈ f.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfxy, inv_mul_cancel]
      rw [hP, Subgroup.mem_bot] at hmem
      exact hxy (inv_mul_eq_one.mp hmem).symm
  intro z hz
  rw [MonoidHom.mem_ker]
  have hfz : f z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := hf q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
  rw [hZ] at hfz
  exact Subgroup.mem_bot.mp hfz

theorem isPGroup_conj [Finite Q] (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker)
    (hQ : PhilipHall.QuaternionBridge.ExLie Q) (g : W) : IsPGroup 2 ↥(conjSub g K) := by
  have hker : f.ker = Subgroup.center W :=
    le_antisymm (ker_le_center h f hf2) (center_le_ker h f hf hf2 hQ)
  let e : W ⧸ Subgroup.center W ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hM : PhilipHall.QuaternionBridge.ExLie (W ⧸ Subgroup.center W) := by
    rcases hQ with hq | hq
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hq)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hq)
  have hZ := Vtx.center_quot_center_eq_bot (Vtx.isSimpleGroup_of_exLie hM)
  have hkZ : k ∉ Subgroup.center W := by
    rw [← hker]
    simpa using not_mem_ker h f hf2 1
  have hk2 : orderOf (QuotientGroup.mk k : W ⧸ Subgroup.center W) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← QuotientGroup.mk_mul, h.invK.sq, QuotientGroup.mk_one]
    · intro h1
      exact hkZ ((QuotientGroup.eq_one_iff k).mp h1)
  have hle := Vtx.oddCent_le_center_of_mk (Vtx.oddCoreIn_centralizer_eq_bot_of_exLie hM hZ hk2)
  have hKC := h.fam.le_centralizer h.memK h.invK
  have hCN := h.fam.tight K h.memK k h.invK
  have hOK : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({k} : Set W)) :=
    le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKC)
      (fun c hc => mem_normalizer_oddCore_of_mem_normalizer (hCN hc)) (oddCoreOf_odd_natCard K)
  have hZ2 := Vtx.isPGroup_center_of_oddFree h.odd
  have hO : oddCoreOf K = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    have hoZ : o ∈ Subgroup.center W := hle (hOK ho)
    exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) ho
      (hZ2.to_le (Subgroup.zpowers_le.mpr hoZ)))
  have h2 : IsPGroup 2 ↥K := by
    intro x
    obtain ⟨n, hn⟩ := h.fam.twoGroup K h.memK (QuotientGroup.mk x)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
    have hx : (x : W) ^ 2 ^ n ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨_, hn⟩
    rw [hO, Subgroup.mem_bot] at hx
    exact Subtype.ext (by simpa using hx)
  exact (h2.map (MulAut.conj g).toMonoidHom : IsPGroup 2 ↥(conjSub g K))

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
