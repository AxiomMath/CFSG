module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Exc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
public import CFSG.Quasithin.H13.U3S1348J
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

section NoCertificates

theorem exists_pow_mul_mem_zpowers_of_mem_sup_zpowers {G : Type} [Group G] {x y z : G}
    (hxy : Commute x y) (hy3 : y ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ k : ℕ, z * y ^ k ∈ Subgroup.zpowers x := by
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hxy.zpow_zpow m n
  obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute hcomm).mp hz
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hpos : (0 : ℤ) < (orderOf y : ℤ) := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hne : orderOf y ≠ 0 := by
      intro h0
      rw [h0] at hdvd
      norm_num at hdvd
    exact_mod_cast Nat.pos_of_ne_zero hne
  let k : ℕ := ((-j) % (orderOf y : ℤ)).toNat
  have hkcast : (k : ℤ) = (-j) % (orderOf y : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
  have hyk : y ^ k = b⁻¹ := by
    calc y ^ k = y ^ ((k : ℤ)) := (zpow_natCast y k).symm
      _ = y ^ ((-j) % (orderOf y : ℤ)) := by rw [hkcast]
      _ = y ^ (-j) := zpow_mod_orderOf y (-j)
      _ = (y ^ j)⁻¹ := zpow_neg y j
      _ = b⁻¹ := by rw [hj]
  have hb_mul : b * y ^ k = 1 := by
    rw [← hj, hyk, ← hj, mul_inv_cancel]
  refine ⟨k, ?_⟩
  have hzk : z * y ^ k = a := by
    rw [hab.symm, mul_assoc, hb_mul, mul_one]
  rw [hzk]
  exact ha

theorem isElemAbelian_closure_three_of_zpowers {G : Type} [Group G] [Finite G]
    {x y z : G} (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x)
    (hzxy : ∀ k : ℕ, z * y ^ k ∉ Subgroup.zpowers x) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({x, y, z} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y, z} : Set G)) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hAx : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hx3
  have hcommAy : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hxy.zpow_left m).eq
  obtain ⟨hAxy, hcardxy⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers hAx hyx hy3 hcommAy
  have hcardxy' : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
    rw [hcardxy, hcardx]
  have hzxy' : z ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    intro hmem
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_zpowers_of_mem_sup_zpowers hxy hy3 hmem
    exact hzxy k hk
  have hcommAB : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hxy.zpow_zpow m n
  have hcommABz : ∀ a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, a * z = z * a := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := (CFSG.mem_sup_of_commute hcommAB).mp ha
    have h1 : Commute a₁ z := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
      exact hxz.zpow_left m
    have h2 : Commute a₂ z := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
      exact hyz.zpow_left n
    exact (h1.mul_left h2).eq
  obtain ⟨hAxyz, hcardxyz⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers hAxy hzxy' hz3 hcommABz
  have hcardxyz' : Nat.card ↥((Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔
      Subgroup.zpowers z) = 27 := by
    rw [hcardxyz, hcardxy']
  have hclosure : Subgroup.closure ({x, y, z} : Set G) =
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers z := by
    have hset : ({x, y, z} : Set G) = {x} ∪ {y} ∪ {z} := by
      ext t
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [hset, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  rw [hclosure]
  exact ⟨hAxyz, hcardxyz'⟩

end NoCertificates


theorem false_of_twF4_torus {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β β₁ β₂ : MulAut S} {n : ℕ} {J : Subgroup S}
    (h : U3CoreHyp S labL β n J) (ht : labL.tag = .twF4)
    (hin₁ : InnDiagKind S labL β₁) (hin₂ : InnDiagKind S labL β₂)
    (h₁ : β₁ ^ 3 = 1) (h₂ : β₂ ^ 3 = 1)
    (hc₁ : Commute β β₁) (hc₂ : Commute β β₂) (hc₁₂ : Commute β₁ β₂)
    (hm₁ : ∃ j ∈ J, β₁ j ≠ j) (hm₂ : ∀ k : ℕ, ∃ j ∈ J, (β₂ * β₁ ^ k) j ≠ j) : False := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rw [ht]
    exact ⟨by decide, by decide, by decide⟩
  obtain ⟨hinn, a, s, hs, hs3, hs1, ha1, hJ, ⟨eSU⟩⟩ := h.twF4_setup ht
  have hβ₁mem : β₁ ∈ innAutDerived S :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived
      h.center_eq_bot hnd hin₁
  have hβ₂mem : β₂ ∈ innAutDerived S :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived
      h.center_eq_bot hnd hin₂
  obtain ⟨s₁, hs₁⟩ := hinn hβ₁mem
  obtain ⟨s₂, hs₂⟩ := hinn hβ₂mem
  have hs₁3 : s₁ ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_pow, hs₁, h₁, map_one]
  have hs₂3 : s₂ ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_pow, hs₂, h₂, map_one]
  have hss₁ : Commute s s₁ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_mul, map_mul, hs, hs₁]
    exact hc₁.eq
  have hss₂ : Commute s s₂ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_mul, map_mul, hs, hs₂]
    exact hc₂.eq
  have hs₁s₂ : Commute s₁ s₂ := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_mul, map_mul, hs₁, hs₂]
    exact hc₁₂.eq
  have hs₁J : s₁ ∈ J := by
    rw [hJ, Subgroup.mem_centralizer_singleton_iff]
    exact hss₁.symm
  have hs₂J : s₂ ∈ J := by
    rw [hJ, Subgroup.mem_centralizer_singleton_iff]
    exact hss₂.symm
  have hcentJ : ∀ t ∈ Subgroup.zpowers s, ∀ j ∈ J, Commute t j := by
    intro t ht j hj
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hsj : Commute s j := by
      rw [hJ] at hj
      exact (Subgroup.mem_centralizer_singleton_iff.mp hj).symm
    exact hsj.zpow_left m
  have hs₁_notin : s₁ ∉ Subgroup.zpowers s := by
    intro hmem
    obtain ⟨j, hjJ, hjne⟩ := hm₁
    refine hjne ?_
    rw [← hs₁, MulAut.conj_apply]
    have hcomm : Commute s₁ j := hcentJ s₁ hmem j hjJ
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hs₂_mul_notin : ∀ k : ℕ, s₂ * s₁ ^ k ∉ Subgroup.zpowers s := by
    intro k hmem
    obtain ⟨j, hjJ, hjne⟩ := hm₂ k
    refine hjne ?_
    have hconj : MulAut.conj (s₂ * s₁ ^ k) = β₂ * β₁ ^ k := by
      rw [map_mul, map_pow, hs₂, hs₁]
    rw [← hconj, MulAut.conj_apply]
    have hcomm : Commute (s₂ * s₁ ^ k) j := hcentJ _ hmem j hjJ
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hs₂_notin : s₂ ∉ Subgroup.zpowers s := by
    have h0 := hs₂_mul_notin 0
    simpa using h0
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hs₁1 : s₁ ≠ 1 := fun h1 => hs₁_notin (h1.symm ▸ Subgroup.one_mem _)
  have hs₂1 : s₂ ≠ 1 := fun h1 => hs₂_notin (h1.symm ▸ Subgroup.one_mem _)
  obtain ⟨hEel, hEcard⟩ :=
    isElemAbelian_closure_three_of_zpowers hss₁ hss₂ hs₁s₂ hs3 hs₁3 hs₂3 hs1
      hs₁_notin hs₂_mul_notin
  let E : Subgroup S := Subgroup.closure ({s, s₁, s₂} : Set S)
  have hEel' : CFSG.Open.IsElemAbelian 3 E := hEel
  have hEcard' : Nat.card E = 27 := hEcard
  have hE_le_cent : E ≤ Subgroup.centralizer ({s} : Set S) := by
    change Subgroup.closure ({s, s₁, s₂} : Set S) ≤
      Subgroup.centralizer ({s} : Set S)
    refine (Subgroup.closure_le (Subgroup.centralizer ({s} : Set S))).mpr ?_
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hss₁.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hss₂.symm
  let φ : ↥E →* ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
      (GaloisField 2 (2 * (2 * a + 1))) 3) :=
    (eSU : ↥(Subgroup.centralizer ({s} : Set S)) →*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
        (GaloisField 2 (2 * (2 * a + 1))) 3)).comp
      (Subgroup.inclusion hE_le_cent)
  let ψ : ↥E →* GL (Fin 3) (GaloisField 2 (2 * (2 * a + 1))) :=
    (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
      (GaloisField 2 (2 * (2 * a + 1))) 3).subtype.comp φ
  let E'' : Subgroup (GL (Fin 3) (GaloisField 2 (2 * (2 * a + 1)))) := ψ.range
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : φ x = φ y :=
      Subgroup.subtype_injective
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
          (GaloisField 2 (2 * (2 * a + 1))) 3) hxy
    exact Subgroup.inclusion_injective hE_le_cent (eSU.injective h1)
  have hcardE'' : Nat.card E'' = Nat.card E := by
    have h := Subgroup.card_map_of_injective (K := ⊤) (f := ψ) hψinj
    rw [Subgroup.map_top, Subgroup.card_top] at h
    simpa [E''] using h
  have hE''comm : ∀ g ∈ E'', ∀ h ∈ E'', g * h = h * g := by
    intro g hg h hh
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    haveI : IsMulCommutative ↥E := hEel'.1
    show ψ x * ψ y = ψ y * ψ x
    rw [← map_mul, ← map_mul, mul_comm' x y]
  have hE''exp : ∀ g ∈ E'', g ^ 3 = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    have hx3 : x ^ 3 = 1 := Subtype.ext (by
      simpa using hEel'.2 (x : S) x.2)
    rw [← map_pow, hx3, map_one]
  have hE''det : ∀ g ∈ E'',
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * (2 * a + 1)))).det = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU (φ x).2
  have hbound : Nat.card E'' ≤ 3 ^ 2 :=
    CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl
      (K := GaloisField 2 (2 * (2 * a + 1))) (ι := Fin 3) (r := 3) Nat.prime_three
      (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
      (by simp) E'' hE''comm hE''exp hE''det
  have hge : 27 ≤ Nat.card E'' := by
    rw [hcardE'', hEcard']
  have hle : Nat.card E'' ≤ 9 := by
    simpa using hbound
  omega

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
