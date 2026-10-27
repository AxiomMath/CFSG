module

public import CFSG.GH74.Generic.S3.LyPump
public import CFSG.GH74.Generic.S3.Lem26Z
public import CFSG.GH74.Generic.S3.L3Class

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section TData

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.Iw_quasisimple (hnd : NbrData G t p f x y Iw Iv) : IsQuasisimple ↥Iw :=
  hnd.comp_w.1.isQuasisimple

theorem NbrData.Iw_le (hnd : NbrData G t p f x y Iw Iv) : Iw ≤ centralizer ({x} : Set G) :=
  hnd.comp_w.1.1

theorem NbrData.x_sq (hnd : NbrData G t p f x y Iw Iv) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hnd.x_inv, pow_two] at this

theorem NbrData.x_ne_one (hnd : NbrData G t p f x y Iw Iv) : x ≠ 1 := fun hx => by
  have := hnd.x_inv
  rw [hx, orderOf_one] at this
  omega

theorem NbrData.y_Iw (hnd : NbrData G t p f x y Iw Iv) : y ∈ Iw := hnd.Iv_le hnd.y_Iv

theorem NbrData.sylow_facts (hnd : NbrData G t p f x y Iw Iv) {R : Subgroup G}
    (hR : IsSylowOf 2 R Iw) :
    IsCyclic ↥(R ⊓ centralizer (R : Set G)) ∧
      ∀ A : Subgroup G, A ≤ normalizer (Iw : Set G) → IsPGroup 2 ↥A →
        (∀ a ∈ A, ∀ r ∈ R, a * r = r * a) →
          ∀ a ∈ A, ∃ z ∈ R ⊓ centralizer (R : Set G), a * z⁻¹ ∈ centralizer (Iw : Set G) := by
  obtain ⟨hcyc, -, -, hksplit⟩ := b_L3_sylow G t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 Iw
    hnd.Iw_quasisimple hnd.odd_w hnd.model_w R hR
  exact ⟨hcyc, hksplit⟩

theorem NbrData.exists_conj_of_involution (hnd : NbrData G t p f x y Iw Iv) {v : G} (hv : v ∈ Iw)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) : ∃ g ∈ Iw, g * y * g⁻¹ = v :=
  b_L3_class G t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 Iw hnd.Iw_quasisimple hnd.odd_w
    hnd.model_w y hnd.y_Iw v hv hnd.y_sq hnd.y_ne_one hv2 hv1

omit [Finite G] in
theorem mem_conjMap_iff {R : Subgroup G} (g a : G) :
    a ∈ R.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * a * g⁻¹ ∈ R := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    have : g * ((MulAut.conj g⁻¹).toMonoidHom r) * g⁻¹ = r := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hr
  · intro h
    refine ⟨g * a * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem NbrData.exists_sylow_central (hnd : NbrData G t p f x y Iw Iv) :
    ∃ P : Subgroup G, IsSylowOf 2 P (centralizer ({x} : Set G)) ∧ y ∈ P ∧ (∀ a ∈ P, a * y = y * a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIw := hnd.comp_w
  have hIwC := hnd.Iw_le
  have hy2 := hnd.y_sq
  obtain ⟨R₁, hR₁, hyR₁⟩ := exists_isSylowOf_ge (K := Iw) (P := Subgroup.zpowers y)
    (Subgroup.zpowers_le.mpr hnd.y_Iw) (isPGroup_zpowers_of_involution hy2)
  have hyR₁' : y ∈ R₁ := hyR₁ (Subgroup.mem_zpowers y)
  have hne : R₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hyR₁'
    exact hnd.y_ne_one hyR₁'
  obtain ⟨v, hvR₁, hv2, hv1, hvc⟩ := exists_central_involution hR₁.isPGroup hne
  obtain ⟨g, hgIw, hg⟩ := hnd.exists_conj_of_involution (hR₁.le hvR₁) hv2 hv1
  set R : Subgroup G := R₁.map (MulAut.conj g⁻¹).toMonoidHom with hRdef
  have hRIw : R ≤ Iw := by
    rintro _ ⟨r, hr, rfl⟩
    have : g⁻¹ * r * g ∈ Iw := Iw.mul_mem (Iw.mul_mem (Iw.inv_mem hgIw) (hR₁.le hr)) hgIw
    simpa using this
  have hRsyl : IsSylowOf 2 R Iw := by
    refine isSylowOf_of_card hRIw ?_
    rw [hRdef, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hR₁.card_eq]
  have hyR : y ∈ R := by
    rw [hRdef, mem_conjMap_iff]
    rw [hg]
    exact hvR₁
  have hyRc : ∀ r ∈ R, r * y = y * r := by
    intro r hr
    rw [hRdef, mem_conjMap_iff] at hr
    have h1 : (g * r * g⁻¹) * v = v * (g * r * g⁻¹) := hvc _ hr
    have hyv : y = g⁻¹ * v * g := by rw [← hg]; group
    calc r * y = g⁻¹ * ((g * r * g⁻¹) * v) * g := by rw [hyv]; group
      _ = g⁻¹ * (v * (g * r * g⁻¹)) * g := by rw [h1]
      _ = y * r := by rw [hyv]; group
  obtain ⟨P, hP, hRP⟩ := exists_isSylowOf_ge (K := centralizer ({x} : Set G)) (P := R)
    (hRIw.trans hIwC) hRsyl.isPGroup
  have hPR : P ⊓ Iw = R := by
    have hPIw : IsSylowOf 2 (P ⊓ Iw) Iw := hP.inf_of_le_normalizer hIwC hIw.le_normalizer
    exact hRsyl.eq_of_le (le_inf hRP hRIw) inf_le_right (hP.isPGroup.to_inf_left)
  obtain ⟨hcyc, -⟩ := hnd.sylow_facts hRsyl
  refine ⟨P, hP, hRP hyR, fun a ha => ?_⟩
  have haC : a ∈ centralizer ({x} : Set G) := hP.le ha
  have hy' : a * y * a⁻¹ ∈ R := by
    rw [← hPR]
    exact ⟨P.mul_mem (P.mul_mem ha (hRP hyR)) (P.inv_mem ha), hIw.conj a haC y hnd.y_Iw⟩
  have hy'c : ∀ r ∈ R, r * (a * y * a⁻¹) = (a * y * a⁻¹) * r := by
    intro r hr
    have hr' : a⁻¹ * r * a ∈ R := by
      rw [← hPR]
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem ha) (hRP hr)) ha, ?_⟩
      have := hIw.conj a⁻¹ ((centralizer ({x} : Set G)).inv_mem haC) r (hRIw hr)
      simpa using this
    have := hyRc _ hr'
    calc r * (a * y * a⁻¹) = a * ((a⁻¹ * r * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * r * a)) * a⁻¹ := by rw [this]
      _ = (a * y * a⁻¹) * r := by group
  have hy'2 : (a * y * a⁻¹) * (a * y * a⁻¹) = 1 := by
    calc (a * y * a⁻¹) * (a * y * a⁻¹) = a * (y * y) * a⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hy'1 : a * y * a⁻¹ ≠ 1 := by
    intro h
    apply hnd.y_ne_one
    have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [this, h]
    group
  have hZ1 : a * y * a⁻¹ ∈ R ⊓ centralizer (R : Set G) :=
    ⟨hy', mem_centralizer_iff.mpr fun r hr => hy'c r hr⟩
  have hZ2 : y ∈ R ⊓ centralizer (R : Set G) :=
    ⟨hyR, mem_centralizer_iff.mpr fun r hr => hyRc r hr⟩
  have heq := eq_of_involutions_of_cyclic hcyc hZ1 hZ2 hy'1 hnd.y_ne_one hy'2 hy2
  calc a * y = (a * y * a⁻¹) * a := by group
    _ = y * a := by rw [heq]

theorem NbrData.involution_cent_Iw {K : Subgroup (CentralizerBar x)}
    (hnd : NbrData G t p f x y Iw Iv) (honly : OnlyInvX x K) (himg : imgBar x Iw = K) {c : G}
    (hcC : c ∈ centralizer ({x} : Set G)) (hcI : c ∈ centralizer (Iw : Set G)) (hcc : c * c = 1) :
    c = 1 ∨ c = x := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcb1 : proj x ⟨c, hcC⟩ ≠ 1 := fun h => hc1 (S45.eq_one_of_proj_eq_one_of_sq hcC h hcc)
  have hcb2 : proj x ⟨c, hcC⟩ * proj x ⟨c, hcC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨c, hcC⟩ : ↥(centralizer ({x} : Set G))) * ⟨c, hcC⟩ = 1 := Subtype.ext hcc
    rw [this, map_one]
  have hord : orderOf (proj x ⟨c, hcC⟩) = 2 := orderOf_eq_prime (by rw [sq]; exact hcb2) hcb1
  have hcent : proj x ⟨c, hcC⟩ ∈ centralizer (K : Set (CentralizerBar x)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← himg] at hk
    obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hk
    have h1 : (g : G) * c = c * (g : G) := Subgroup.mem_centralizer_iff.1 hcI (g : G) hg
    have h2 : g * ⟨c, hcC⟩ = ⟨c, hcC⟩ * g := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  have h1 := honly _ hcent hord
  have hxb : xbar x = proj x ⟨x, hxC⟩ := rfl
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have habz : c * x ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem hcC hxC
  have hab2 : (c * x) * (c * x) = 1 := by
    calc (c * x) * (c * x) = c * (x * c) * x := by group
      _ = c * (c * x) * x := by rw [hcx]
      _ = (c * c) * (x * x) := by group
      _ = 1 := by rw [hcc, hnd.x_sq, one_mul]
  have him : proj x ⟨c * x, habz⟩ = 1 := by
    have : (⟨c * x, habz⟩ : ↥(centralizer ({x} : Set G))) = ⟨c, hcC⟩ * ⟨x, hxC⟩ := rfl
    rw [this, map_mul, h1, ← hxb]
    exact xbar_mul_self hnd.x_inv
  have h3 := S45.eq_one_of_proj_eq_one_of_sq habz him hab2
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hnd.x_sq
  calc c = c * x * x⁻¹ := by group
    _ = x := by rw [h3, one_mul, hx']

theorem NbrData.involution_center_cases {K : Subgroup (CentralizerBar x)}
    (hnd : NbrData G t p f x y Iw Iv) (honly : OnlyInvX x K) (himg : imgBar x Iw = K)
    {P : Subgroup G} (hP : IsSylowOf 2 P (centralizer ({x} : Set G))) (hyP : y ∈ P)
    (hyc : ∀ a ∈ P, a * y = y * a) :
    ∀ z ∈ P, (∀ a ∈ P, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hzP hzc hzz
  have hIw := hnd.comp_w
  have hIwC := hnd.Iw_le
  have hR : IsSylowOf 2 (P ⊓ Iw) Iw := hP.inf_of_le_normalizer hIwC hIw.le_normalizer
  obtain ⟨hcyc, hksplit⟩ := hnd.sylow_facts hR
  have hzN : z ∈ normalizer (Iw : Set G) := hIw.le_normalizer (hP.le hzP)
  have hAN : Subgroup.zpowers z ≤ normalizer (Iw : Set G) := Subgroup.zpowers_le.mpr hzN
  have hAcent : ∀ a ∈ Subgroup.zpowers z, ∀ r ∈ P ⊓ Iw, a * r = r * a := by
    intro a ha r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute z r := (hzc r hr.1).symm
    exact (hcomm.zpow_left k).eq
  obtain ⟨z', hz'R, hz'c⟩ := hksplit (Subgroup.zpowers z) hAN
    (isPGroup_zpowers_of_involution hzz) hAcent z (Subgroup.mem_zpowers z)
  have hz'P : z' ∈ P := hz'R.1.1
  have hz'I : z' ∈ Iw := hz'R.1.2
  set c : G := z * z'⁻¹ with hc
  have hcP : c ∈ P := P.mul_mem hzP (P.inv_mem hz'P)
  have hzc' : z = c * z' := by rw [hc]; group
  have hcz' : z' * c = c * z' := mem_centralizer_iff.mp hz'c z' hz'I
  have h1 : c * c * (z' * z') = 1 := by
    have hcomm : Commute z' c := hcz'
    have := hcomm.mul_mul_mul_comm c z'
    rw [← this, ← hzc']
    exact hzz
  have hzz' : z' * z' = 1 := by
    have hu : z' * z' = (c * c)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : (⟨z' * z', Iw.mul_mem hz'I hz'I⟩ : ↥Iw) ∈ center ↥Iw := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcc : (c * c) ∈ centralizer (Iw : Set G) :=
        (centralizer (Iw : Set G)).mul_mem hz'c hz'c
      have : ((c * c)⁻¹) ∈ centralizer (Iw : Set G) := (centralizer (Iw : Set G)).inv_mem hcc
      rw [← hu] at this
      exact mem_centralizer_iff.mp this g g.2
    have hRz : z' * z' ∈ P ⊓ Iw := (P ⊓ Iw).mul_mem hz'R.1 hz'R.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR.isPGroup) ⟨z' * z', hRz⟩
    have hk' : orderOf (⟨z' * z', Iw.mul_mem hz'I hz'I⟩ : ↥Iw) = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨z' * z', hRz⟩ : ↥(P ⊓ Iw))]
    have := eq_one_of_odd_center_of_two_power hnd.odd_w hmem hk'
    exact congrArg Subtype.val this
  have hcc : c * c = 1 := by
    rwa [hzz', mul_one] at h1
  have hcx : c = 1 ∨ c = x := hnd.involution_cent_Iw honly himg (hP.le hcP) hz'c hcc
  have hvZ : y ∈ (P ⊓ Iw) ⊓ centralizer ((P ⊓ Iw : Subgroup G) : Set G) :=
    ⟨⟨hyP, hnd.y_Iw⟩, mem_centralizer_iff.mpr fun r hr => hyc r hr.1⟩
  have hz'y : z' = 1 ∨ z' = y := by
    by_cases hz'1 : z' = 1
    · exact Or.inl hz'1
    · exact Or.inr (eq_of_involutions_of_cyclic hcyc hz'R hvZ hz'1 hnd.y_ne_one hzz' hnd.y_sq)
  rw [hzc']
  rcases hcx with h1 | h1 <;> rcases hz'y with h2 | h2
  · left; rw [h1, h2, mul_one]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2, hnd.comm]

theorem NbrData.x_mem_sylow (hnd : NbrData G t p f x y Iw Iv) {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({x} : Set G))) : x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xC : ↥(centralizer ({x} : Set G)) := ⟨x, hxC⟩ with hxCdef
  have hxx : xC * xC = 1 := Subtype.ext hnd.x_sq
  have hcen : ∀ g : ↥(centralizer ({x} : Set G)), g * xC = xC * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hN : (Subgroup.zpowers xC).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g xC := hcen g
    have : g * xC ^ k * g⁻¹ = xC ^ k := by
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  have hle : Subgroup.zpowers xC ≤ (S : Subgroup ↥(centralizer ({x} : Set G))) :=
    IsPGroup.le_sylow_of_normal (isPGroup_zpowers_of_involution hxx) S
  have hmem : xC ∈ (S : Subgroup ↥(centralizer ({x} : Set G))) := hle (Subgroup.mem_zpowers xC)
  rw [hS] at hmem
  exact hmem

theorem NbrData.x_mem_commutator {K : Subgroup (CentralizerBar x)} (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hnd : NbrData G t p f x y Iw Iv) (honly : OnlyInvX x K)
    (himg : imgBar x Iw = K) (hxy : IsConj x (y * x)) (hnc : ¬ IsConj y x) :
    ∃ hx : x ∈ centralizer ({y} : Set G),
      (⟨x, hx⟩ : ↥(centralizer ({y} : Set G))) ∈ commutator ↥(centralizer ({y} : Set G)) := by
  obtain ⟨P, hP, hyP, hyc⟩ := hnd.exists_sylow_central
  have hcases := hnd.involution_center_cases honly himg hP hyP hyc
  have hxP : x ∈ P := hnd.x_mem_sylow hP
  have hweak : ∀ z : G, z ∈ P → (∀ a ∈ P, a * z = z * a) → z * z = 1 →
      (∃ g : G, g * y * g⁻¹ = z) → z = y := by
    intro z hzP hzc hzz ⟨g, hg⟩
    rcases hcases z hzP hzc hzz with h | h | h | h
    · exfalso
      apply hnd.y_ne_one
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, hg, h]
      group
    · exact absurd (isConj_iff.mpr ⟨g, hg.trans h⟩) hnc
    · exact h
    · exact absurd ((isConj_iff.mpr ⟨g, hg.trans h⟩).trans hxy.symm) hnc
  have hcen := exists_sylow_central_of_weakly_closed hP hxP hyP hyc hnd.y_sq hweak
  refine S45.b_III8_6_3 G hsimple hnonab x hnd.x_inv P hP y hyP hyc hnd.y_inv hcen ?_
  intro g hgP hgc
  have hz2 : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
    calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hnd.y_sq]; group
  exact ⟨1, Subgroup.one_mem _, by rw [hweak _ hgP hgc hz2 ⟨g, rfl⟩]; group⟩

end TData

end CFSG.GH74.Generic.S3
