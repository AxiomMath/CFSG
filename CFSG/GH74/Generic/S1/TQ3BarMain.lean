module

public import CFSG.GH74.Generic.S1.TQ3BarVert
public import CFSG.GH74.Generic.S1.TQ3BarDiag
public import CFSG.GH74.Generic.S1.RQ3Odd
public import CFSG.GH74.Generic.S45.LDiagCore
public import CFSG.GH74.Generic.Sections

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

variable {G : Type} [Group G] [Finite G]

theorem lift_perfect_cent {c t : G} (ht2 : t * t = 1) (htc : t ∈ centralizer ({c} : Set G))
    {P : Subgroup (CentralizerBar c)} (hP : ⁅P, P⁆ = P)
    (hPc : ∀ z ∈ P, z * barOf htc = barOf htc * z) :
    ∃ Q : Subgroup G, ⁅Q, Q⁆ = Q ∧ Q ≤ centralizer ({t} : Set G) ⊓ centralizer ({c} : Set G) ∧
      S45.barSub c Q = P := by
  set Y := centralizer ({c} : Set G) with hY
  set u : ↥Y := ⟨t, htc⟩ with hu
  have hu2 : u * u = 1 := Subtype.ext ht2
  set U : Subgroup ↥Y := centralizer ({u} : Set ↥Y) with hU
  let f : ↥U →* CentralizerBar c := (proj c).comp U.subtype
  have hPf : P ≤ f.range := by
    intro z hz
    obtain ⟨g, hgu, hgz⟩ := proj_cent c hu2 z (hPc z hz)
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 hgu⟩, hgz⟩
  obtain ⟨Q', hQ'perf, hQ'map⟩ := CFSG.GH74.Generic.S45.exists_perfect_lift_hom f hP hPf
  refine ⟨(Q'.map U.subtype).map Y.subtype, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hQ'perf]
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨?_, (q : ↥Y).2⟩
    show ((q : ↥Y) : G) ∈ centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 q.2
    exact congrArg Subtype.val this
  · unfold S45.barSub
    have h1 : ((Q'.map U.subtype).map Y.subtype).subgroupOf Y = Q'.map U.subtype :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    rw [h1, Subgroup.map_map]
    exact hQ'map


theorem pumpup_dichotomy {c s : G} (hs : orderOf s = 2) (hsc : s ∈ centralizer ({c} : Set G))
    {B : Subgroup G}
    (hB : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({s} : Set G) ⊓ centralizer ({c} : Set G)) B) :
    ∃ L : Subgroup (CentralizerBar c), IsComponent L ∧
      ((conjSub (proj c ⟨s, hsc⟩)⁻¹ L = L ∧ S45.barSub c B ≤ L) ∨
        (conjSub (proj c ⟨s, hsc⟩)⁻¹ L ≠ L ∧
          ∃ hAB : ⁅L, conjSub (proj c ⟨s, hsc⟩)⁻¹ L⁆ = ⊥,
            S45.barSub c B ≤ (swapDiag hAB).range)) := by
  have hs' := CFSG.GH74.GLS.TwoThin.orderOf_mk_centralizer hsc hs
  have hΛC := CFSG.GH74.GLS.TwoThin.le_centralizer_mk hB.1 hsc
  have hΛ := CFSG.GH74.GLS.TwoThin.isTwoComponent_centralizer_mk hB hsc
  obtain ⟨-, -, M, hM, hcases, -⟩ := CFSG.GH74.GLS.TwoThin.pumpupY_structure hs' hΛC hΛ
  exact ⟨M, hM, hcases⟩


omit [Finite G] in
theorem oddGenerated_barSub {c : G} {J : Subgroup G} (hJC : J ≤ centralizer ({c} : Set G))
    (hJ : OddGenerated J) : OddGenerated (S45.barSub c J) := by
  have h1 : OddGenerated (J.subgroupOf (centralizer ({c} : Set G))) := by
    refine oddGenerated_comap (centralizer ({c} : Set G)).subtype_injective hJ ?_
    rw [Subgroup.range_subtype]
    exact hJC
  exact oddGenerated_map (proj c) h1

theorem q8_barSub {c : G} {J : Subgroup G} (hJC : J ≤ centralizer ({c} : Set G)) (φ : Q8 →* G)
    (hφ : Function.Injective φ) (hφJ : ∀ g, φ g ∈ J) :
    ∃ φ' : Q8 →* CentralizerBar c, Function.Injective φ' ∧ ∀ g, φ' g ∈ S45.barSub c J := by
  let φ₀ : Q8 →* ↥(centralizer ({c} : Set G)) :=
    φ.codRestrict (centralizer ({c} : Set G)) (fun g => hJC (hφJ g))
  refine ⟨(proj c).comp φ₀, ?_, fun g => S45.proj_mem_barSub (hJC (hφJ g)) (hφJ g)⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hodd := proj_odd c (φ₀ g) hg
  have hq4 : ∀ g : Q8, g ^ 4 = 1 := by decide
  have h4 : orderOf (φ₀ g) ∣ 2 ^ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have : φ₀ (g ^ 4) = 1 := by rw [hq4 g, map_one]
    simpa [map_pow] using this
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  have hi0 : i = 0 := by
    by_contra hne
    have : Even (orderOf (φ₀ g)) := by
      rw [hio]
      exact (Nat.even_pow.2 ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hi0, pow_zero] at hio
  have h1 : φ₀ g = 1 := orderOf_eq_one_iff.1 hio
  apply hφ
  rw [map_one]
  have := congrArg Subtype.val h1
  exact this


structure Q3Cfg (G : Type) [Group G] (F : Type) [Field F] (c x X2 y : G) (A J : Subgroup G) : Prop where
  c2 : orderOf c = 2
  x2 : orderOf x = 2
  X2_2 : orderOf X2 = 2
  y_sq : y * y = 1
  y_ne : y ≠ 1
  hxc : x ∈ centralizer ({c} : Set G)
  hX2c : X2 ∈ centralizer ({c} : Set G)
  hyc : y ∈ centralizer ({c} : Set G)
  x_eq : x = y * c
  y_mem : y ∈ A
  A_quasi : IsQuasisimple ↥A
  A_equiv : Nonempty (↥A ≃* SL(3, F))
  A_cen : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → z = 1
  A_V : A ≤ centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G)
  perf2 : ∀ Q : Subgroup G, Q ≤ centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G) →
    ⁅Q, Q⁆ = Q → Q ≤ A
  perfx : ∀ Q : Subgroup G, Q ≤ centralizer ({x} : Set G) ⊓ centralizer ({c} : Set G) →
    ⁅Q, Q⁆ = Q → Q = ⊥
  J_C : J ≤ centralizer ({c} : Set G)
  J_A : ∀ a ∈ A, ∀ j ∈ J, a * j = j * a
  J_odd : OddGenerated J
  q8J : ∃ φ : Q8 →* G, Function.Injective φ ∧ ∀ g, φ g ∈ J
  q8A : ∃ φ : Q8 →* G, Function.Injective φ ∧ ∀ g, φ g ∈ A

theorem q3_main (hK : KL3Table) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hkgh : KGH G) (hgen : Gen4 G) {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    {c x X2 y : G} {A J : Subgroup G} (cfg : Q3Cfg G F c x X2 y A J) :
    (S45.barSub c A).IsSubnormal := by
  classical
  have hH : Gen4 (CentralizerBar c) := gen4_centralizerBar hgen c
  have hAC : A ≤ centralizer ({c} : Set G) := fun a ha => (Subgroup.mem_inf.1 (cfg.A_V ha)).2
  have hy2 : orderOf y = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact cfg.y_sq) cfg.y_ne
  have hAZ : center ↥A = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have := cfg.A_cen z.1 z.2 (fun w hw => congrArg Subtype.val
      ((Subgroup.mem_center_iff.1 hz) ⟨w, hw⟩).symm)
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hAsimple : IsSimpleGroup ↥A := by
    have e : ↥A ⧸ center ↥A ≃* ↥A :=
      (QuotientGroup.quotientMulEquivOfEq hAZ).trans QuotientGroup.quotientBot
    have := cfg.A_quasi.2.1
    exact e.symm.isSimpleGroup
  obtain ⟨φA, hφA⟩ := CFSG.GH74.Generic.S45.barSub_mulEquiv hAC hAsimple cfg.y_mem cfg.y_sq cfg.y_ne
  have hA'q : IsQuasisimple ↥(S45.barSub c A) := isQuasisimple_of_mulEquiv φA cfg.A_quasi
  obtain ⟨eA⟩ := cfg.A_equiv
  have hA'e : Nonempty (↥(S45.barSub c A) ≃* SL(3, F)) := ⟨φA.symm.trans eA⟩
  have hA'cen : ∀ z ∈ S45.barSub c A, (∀ w ∈ S45.barSub c A, z * w = w * z) → z = 1 := by
    intro z hz hzc
    have hz' : ∃ a : ↥A, ((φA a : ↥(S45.barSub c A)) : CentralizerBar c) = z := by
      obtain ⟨a, ha⟩ := φA.surjective ⟨z, hz⟩
      exact ⟨a, by rw [ha]⟩
    obtain ⟨a, rfl⟩ := hz'
    have : a = 1 := by
      apply Subtype.ext
      apply cfg.A_cen a.1 a.2
      intro w hw
      have := hzc (φA ⟨w, hw⟩) (φA ⟨w, hw⟩).2
      have h2 : φA a * φA ⟨w, hw⟩ = φA ⟨w, hw⟩ * φA a := Subtype.ext this
      have h3 : a * ⟨w, hw⟩ = ⟨w, hw⟩ * a := φA.injective (by rw [map_mul, map_mul]; exact h2)
      exact congrArg Subtype.val h3
    rw [this, map_one]
    rfl
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp cfg.A_quasi.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [cfg.x2] at this
    rw [← sq]
    exact this
  have hX22 : X2 * X2 = 1 := by
    have := pow_orderOf_eq_one X2
    rw [cfg.X2_2] at this
    rw [← sq]
    exact this
  have hc22 : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rw [cfg.c2] at this
    rw [← sq]
    exact this
  have hcc : c ∈ centralizer ({c} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcbcen : ∀ h : CentralizerBar c, h * proj c ⟨c, hcc⟩ = proj c ⟨c, hcc⟩ * h := by
    intro h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective h
    show proj c k * proj c ⟨c, hcc⟩ = proj c ⟨c, hcc⟩ * proj c k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 k.2)
  have hnormA : ∀ g ∈ centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G), ∀ u ∈ A,
      g * u * g⁻¹ ∈ A := by
    intro g hg u hu
    have hle : A.map (MulAut.conj g).toMonoidHom ≤
        centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      exact (centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G)).mul_mem
        ((centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G)).mul_mem hg (cfg.A_V ha))
        ((centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G)).inv_mem hg)
    have hperf : ⁅A.map (MulAut.conj g).toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ =
        A.map (MulAut.conj g).toMonoidHom := by
      rw [← Subgroup.map_commutator, hAperf]
    exact cfg.perf2 _ hle hperf ⟨u, hu, by simp [MulAut.conj_apply]⟩
  have hpc : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X2} : Set G) ⊓ centralizer ({c} : Set G)) A :=
    isPCompIn_of_normal_block cfg.A_V hnormA cfg.A_quasi
  obtain ⟨L, hL, hcases⟩ := pumpup_dichotomy cfg.X2_2 cfg.hX2c hpc
  obtain ⟨φ, hφ, hφJ⟩ := cfg.q8J
  obtain ⟨φ', hφ', hφ'J⟩ := q8_barSub cfg.J_C φ hφ hφJ
  have hJodd' : OddGenerated (S45.barSub c J) := oddGenerated_barSub cfg.J_C cfg.J_odd
  have hJA' : ∀ a ∈ S45.barSub c A, ∀ j ∈ S45.barSub c J, a * j = j * a := by
    intro a ha j hj
    obtain ⟨g, hg, hgA, rfl⟩ := S45.mem_barSub.1 ha
    obtain ⟨h, hh, hhJ, rfl⟩ := S45.mem_barSub.1 hj
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (cfg.J_A g hgA h hhJ)
  rcases hcases with ⟨-, hAL⟩ | ⟨hne, hAB, hAdiag⟩
  ·
    have hGH : GHList (↥L ⧸ center ↥L) := ghList_of_quasisimple hs hn hkgh cfg.c2 hL.1
    have hyA' : proj c ⟨y, cfg.hyc⟩ ∈ S45.barSub c A := S45.proj_mem_barSub cfg.hyc cfg.y_mem
    have hy2' : orderOf (proj c ⟨y, cfg.hyc⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, ← map_mul]
        have : (⟨y, cfg.hyc⟩ : ↥(centralizer ({c} : Set G))) * ⟨y, cfg.hyc⟩ = 1 :=
          Subtype.ext cfg.y_sq
        rw [this, map_one]
      · intro h
        exact cfg.y_ne (S45.eq_one_of_proj_eq_one_of_sq cfg.hyc h cfg.y_sq)
    have hsolv : ∀ P : Subgroup (CentralizerBar c),
        P ≤ centralizer ({proj c ⟨y, cfg.hyc⟩} : Set (CentralizerBar c)) → ⁅P, P⁆ = P → P = ⊥ := by
      intro P hP hPperf
      have hxbar : barOf cfg.hxc = proj c ⟨y, cfg.hyc⟩ * proj c ⟨c, hcc⟩ := by
        show proj c ⟨x, cfg.hxc⟩ = _
        rw [← map_mul]
        congr 1
        exact Subtype.ext cfg.x_eq
      have hPc : ∀ z ∈ P, z * barOf cfg.hxc = barOf cfg.hxc * z := by
        intro z hz
        have h1 : z * proj c ⟨y, cfg.hyc⟩ = proj c ⟨y, cfg.hyc⟩ * z :=
          Subgroup.mem_centralizer_singleton_iff.1 (hP hz)
        rw [hxbar]
        calc z * (proj c ⟨y, cfg.hyc⟩ * proj c ⟨c, hcc⟩)
            = (z * proj c ⟨y, cfg.hyc⟩) * proj c ⟨c, hcc⟩ := by rw [mul_assoc]
          _ = (proj c ⟨y, cfg.hyc⟩ * z) * proj c ⟨c, hcc⟩ := by rw [h1]
          _ = proj c ⟨y, cfg.hyc⟩ * (z * proj c ⟨c, hcc⟩) := by rw [mul_assoc]
          _ = proj c ⟨y, cfg.hyc⟩ * (proj c ⟨c, hcc⟩ * z) := by rw [hcbcen z]
          _ = (proj c ⟨y, cfg.hyc⟩ * proj c ⟨c, hcc⟩) * z := by rw [mul_assoc]
      obtain ⟨Q, hQperf, hQle, hQP⟩ := lift_perfect_cent hx2 cfg.hxc hPperf hPc
      have hQ := cfg.perfx Q hQle hQperf
      rw [← hQP, hQ]
      unfold S45.barSub
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    have hAL' := vertical_case hH hK hF3 hL hGH hAL hA'q hA'e hyA' hy2' hsolv hJodd' hJA' φ' hφ' hφ'J
    rw [hAL']
    exact hL.2
  ·
    exfalso
    obtain ⟨ψ, hψ, hψA⟩ := cfg.q8A
    obtain ⟨ψ', hψ', hψ'A⟩ := q8_barSub hAC ψ hψ hψA
    have hσ2 : proj c ⟨X2, cfg.hX2c⟩ * proj c ⟨X2, cfg.hX2c⟩ = 1 := by
      rw [← map_mul]
      have : (⟨X2, cfg.hX2c⟩ : ↥(centralizer ({c} : Set G))) * ⟨X2, cfg.hX2c⟩ = 1 :=
        Subtype.ext hX22
      rw [this, map_one]
    have hperfH : ∀ P : Subgroup (CentralizerBar c),
        P ≤ centralizer ({proj c ⟨X2, cfg.hX2c⟩} : Set (CentralizerBar c)) → ⁅P, P⁆ = P →
          P ≤ S45.barSub c A := by
      intro P hP hPperf
      have hPc : ∀ z ∈ P, z * barOf cfg.hX2c = barOf cfg.hX2c * z := fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.1 (hP hz)
      obtain ⟨Q, hQperf, hQle, hQP⟩ := lift_perfect_cent hX22 cfg.hX2c hPperf hPc
      rw [← hQP]
      exact S45.barSub_mono (cfg.perf2 Q hQle hQperf)
    exact q3_false_of_diag hH hσ2 hL hne hAB hAdiag hperfH hA'cen hJodd' hJA' φ' hφ' hφ'J ψ' hψ'
      hψ'A

end CFSG.GH74.Generic.S1