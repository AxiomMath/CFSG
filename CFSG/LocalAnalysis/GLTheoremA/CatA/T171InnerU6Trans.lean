module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section PiL

variable {Ω : Type} [Group Ω] {L : Subgroup Ω}

@[expose] noncomputable def piL (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) : ↥L →* S6 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem piL_apply (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) (l : ↥L) :
    piL e l = e (QuotientGroup.mk l) := rfl

theorem piL_surjective (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) :
    Function.Surjective (piL e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))

theorem ker_piL (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) :
    (piL e).ker = Subgroup.center ↥L := by
  ext l
  rw [MonoidHom.mem_ker, piL_apply, ← e.map_one]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff l).mp (e.injective h)
  · intro h
    rw [(QuotientGroup.eq_one_iff l).mpr h, map_one]

@[expose] noncomputable def imL (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) (H : Subgroup Ω) :
    Subgroup S6 :=
  (H.subgroupOf L).map (piL e)

end PiL

section Theta

variable {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]

theorem theta_piL (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) (g : Ω) (l : ↥L) :
    theta L e g (piL e l) =
      piL e ⟨g * l * g⁻¹, (inferInstance : L.Normal).conj_mem _ l.2 g⟩ := by
  change autTr e (CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L g) (piL e l) = _
  rw [autTr_apply]
  change e (CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L g (e.symm (piL e l))) = _
  rw [show e.symm (piL e l) = QuotientGroup.mk' (Subgroup.center ↥L) l from
    MulEquiv.symm_apply_apply e _]
  rw [CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom_apply_mk, piL_apply]
  congr 1

theorem theta_coe (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) (l : ↥L) :
    theta L e (l : Ω) = MulAut.conj (piL e l) := by
  ext s
  obtain ⟨l', rfl⟩ := piL_surjective e s
  rw [theta_piL, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem theta_eq_one_iff [Group.IsPerfect ↥L]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) (g : Ω) :
    theta L e g = 1 ↔ g ∈ Subgroup.centralizer (L : Set Ω) := by
  have h1 : theta L e g = 1 ↔
      CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L g = 1 := by
    change autTr e (CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L g) = 1 ↔ _
    rw [← map_one (autTr e)]
    exact (autTr_injective e).eq_iff
  have h2 : CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L g = 1 ↔
      MulAut.conjNormal (H := L) g = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L)
      (MulAut.conjNormal (H := L) g) = 1 ↔ _
    rw [← map_one (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L)]
    exact (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      ↥L).eq_iff
  rw [h1, h2]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h' : (MulAut.conjNormal (H := L) g) ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [h]; rfl
    have hgl : g * l * g⁻¹ = l := by
      have := congrArg (fun x : ↥L => (x : Ω)) h'
      simpa using this
    exact (show g * l = l * g from by
      calc g * l = (g * l * g⁻¹) * g := by group
        _ = l * g := by rw [hgl]).symm
  · intro hg
    rw [Subgroup.mem_centralizer_iff] at hg
    ext l
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hgl : g * (l : Ω) = (l : Ω) * g := (hg l l.2).symm
    calc g * (l : Ω) * g⁻¹ = ((l : Ω) * g) * g⁻¹ := by rw [hgl]
      _ = (l : Ω) := by group

end Theta

theorem Psi_iota (s : S6) : Psi (iota s) = MulAut.conj s := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
  rw [iota_mk, Psi_mk]
  ext w
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  rw [Psi0_mk (Subgroup.inclusion Gu_of_SU u) v (conjM6 (Subgroup.inclusion Gu_of_SU u) v)
    (conjM6_apply _ _), MulAut.conj_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem iota_Psi (g : PGU6) (s : S6) : iota (Psi g s) = g * iota s * g⁻¹ := by
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
  rw [Psi_mk]
  exact iota_Psi0 ĝ (QuotientGroup.mk u)

section Bt

variable {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]

theorem mem_Bt (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {B : Subgroup Ω} {g : PGU6} :
    g ∈ Bt B L e ↔ ∃ b ∈ B, theta L e b = Psi g := by
  rw [Bt, Subgroup.mem_comap, Subgroup.mem_map]

theorem exists_mem_Bt (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {B : Subgroup Ω}
    (hB : ∀ b ∈ B, b ^ 3 = 1) {b : Ω} (hb : b ∈ B) :
    ∃ g ∈ Bt B L e, Psi g = theta L e b := by
  have h3 : theta L e b ^ 3 = 1 := by rw [← map_pow, hB b hb, map_one]
  obtain ⟨g, hg⟩ := exists_Psi_of_pow_three (theta L e b) h3
  exact ⟨g, (mem_Bt e).mpr ⟨b, hb, hg.symm⟩, hg⟩

theorem isElemAbelian_Bt (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {B : Subgroup Ω}
    (hB : IsElemAbelian 3 B) : IsElemAbelian 3 (Bt B L e) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨b1, hb1B, hb1⟩ := (mem_Bt e).mp a.2
    obtain ⟨b2, hb2B, hb2⟩ := (mem_Bt e).mp b.2
    have h12 : b1 * b2 = b2 * b1 :=
      congrArg (fun x : ↥B => (x : Ω)) (hB.1.is_comm.comm ⟨b1, hb1B⟩ ⟨b2, hb2B⟩)
    apply Subtype.ext
    refine Psi_injective (show Psi ((a : PGU6) * b) = Psi ((b : PGU6) * a) from ?_)
    calc Psi ((a : PGU6) * b) = Psi a * Psi b := map_mul _ _ _
      _ = theta L e b1 * theta L e b2 := by rw [hb1, hb2]
      _ = theta L e (b1 * b2) := (map_mul _ _ _).symm
      _ = theta L e (b2 * b1) := by rw [h12]
      _ = theta L e b2 * theta L e b1 := map_mul _ _ _
      _ = Psi b * Psi a := by rw [hb1, hb2]
      _ = Psi (b * a) := (map_mul _ _ _).symm
  · obtain ⟨b, hbB, hb⟩ := (mem_Bt e).mp ha
    refine Psi_injective (show Psi (a ^ 3) = Psi 1 from ?_)
    rw [map_pow, map_one, ← hb, ← map_pow, hB.2 b hbB, map_one]

theorem isPerfect_of_cfg [Finite Ω] {B : Subgroup Ω} {x : Ω}
    (hc : S171.Cfg Ω 3 B x L) : Group.IsPerfect ↥L :=
  ⟨hc.qs.1⟩

theorem card_Bt [Finite Ω] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {B : Subgroup Ω} {x : Ω}
    (hc : S171.Cfg Ω 3 B x L) : Nat.card (Bt B L e) * 3 = Nat.card B := by
  haveI hperf : Group.IsPerfect ↥L := isPerfect_of_cfg hc
  haveI : Fact (Nat.Prime 3) := ⟨hc.prime⟩
  have hC : B ⊓ (theta L e).ker = Subgroup.zpowers x := by
    ext b
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hb, h1⟩
      rw [theta_eq_one_iff] at h1
      exact (hc.cent b hb).mp h1
    · intro hb
      have hbB : b ∈ B := Subgroup.zpowers_le.mpr hc.mem hb
      refine ⟨hbB, ?_⟩
      rw [theta_eq_one_iff]
      exact (hc.cent b hbB).mpr hb
  have hcardC : Nat.card (B ⊓ (theta L e).ker : Subgroup Ω) = 3 := by
    rw [hC, Nat.card_zpowers]
    exact orderOf_eq_prime_iff.mpr ⟨hc.elem.2 x hc.mem, hc.ne_one⟩
  let f : ↥B →* MulAut S6 := (theta L e).comp B.subtype
  have hker : f.ker = (B ⊓ (theta L e).ker).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card f.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hcardC]
  have hrange : f.range = B.map (theta L e) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, b.2, hb⟩, fun ⟨b, hbB, hb⟩ => ⟨⟨b, hbB⟩, hb⟩⟩
  let ψ : ↥(Bt B L e) → ↥(B.map (theta L e)) := fun g => ⟨Psi g, g.2⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨?_, ?_⟩
    · intro g1 g2 h
      apply Subtype.ext
      exact Psi_injective (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      rw [Subgroup.mem_map] at hy
      obtain ⟨b, hbB, rfl⟩ := hy
      have hb3 : b ^ 3 = 1 := hc.elem.2 b hbB
      have hθ3 : theta L e b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
      obtain ⟨g, hg⟩ := exists_Psi_of_pow_three (theta L e b) hθ3
      refine ⟨⟨g, (mem_Bt e).mpr ⟨b, hbB, hg.symm⟩⟩, Subtype.ext hg⟩
  have hcardBt : Nat.card (Bt B L e) = Nat.card (B.map (theta L e)) :=
    Nat.card_congr (Equiv.ofBijective ψ hψ)
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hcardker, hrange, ← hcardBt] at h1
  simpa [Nat.mul_comm] using h1

end Bt

section Inner

variable {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]

theorem inducesInnerMod_of_theta_eq_conj [Group.IsPerfect ↥L]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {b : Ω} {s : S6}
    (h : theta L e b = MulAut.conj s) : InducesInnerMod 3 L b := by
  obtain ⟨l, hl⟩ := piL_surjective e s
  refine ⟨l, l.2, fun y hy => ?_⟩
  have hθ : theta L e (b * (l : Ω)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, theta_coe, hl, mul_inv_cancel]
  have hc : b * (l : Ω)⁻¹ ∈ Subgroup.centralizer (L : Set Ω) := by
    rw [← theta_eq_one_iff]
    exact hθ
  have hcomm : ∀ y ∈ L, y * (b * (l : Ω)⁻¹) = (b * (l : Ω)⁻¹) * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp hc y hy
  have h1 : b * (l : Ω)⁻¹ * y * (b * (l : Ω)⁻¹)⁻¹ = y := by
    rw [← hcomm y hy]
    group
  have hconj : (l : Ω)⁻¹ * y * l = b⁻¹ * y * b := by
    calc (l : Ω)⁻¹ * y * l
        = b⁻¹ * (b * (l : Ω)⁻¹ * y * (b * (l : Ω)⁻¹)⁻¹) * b := by group
      _ = b⁻¹ * y * b := by rw [h1]
  rw [hconj, inv_mul_cancel]
  exact Subgroup.one_mem _

end Inner

section Image

variable {Ω : Type} [Group Ω] {L : Subgroup Ω}

theorem imL_le_fixSubgroup [L.Normal] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {H : Subgroup Ω}
    {g : Ω} (hg : ∀ h ∈ H, g * h = h * g) :
    imL e H ≤ fixSubgroup (theta L e g) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_fixSubgroup, theta_piL]
  congr 1
  apply Subtype.ext
  change g * (l : Ω) * g⁻¹ = (l : Ω)
  rw [hg (l : Ω) hl]
  group

theorem imL_perfect (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {H : Subgroup Ω}
    (hHL : H ≤ L) (hH : ⁅H, H⁆ = H) : ⁅imL e H, imL e H⁆ = imL e H := by
  have hK : ⁅H.subgroupOf L, H.subgroupOf L⁆ = H.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator]
    simp only [Subgroup.map_subgroupOf_eq_of_le hHL, hH]
  have hmap := Subgroup.map_commutator (piL e)
    (H₁ := H.subgroupOf L) (H₂ := H.subgroupOf L)
  rw [hK] at hmap
  exact hmap.symm

theorem card_imL [Finite Ω] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {K : Subgroup Ω}
    (hKL : K ≤ L) (hK : IsSimpleGroup ↥K) (hKperf : ⁅K, K⁆ = K) :
    Nat.card (imL e K) = Nat.card K := by
  let f : ↥K →* S6 := (piL e).comp (Subgroup.inclusion hKL)
  have hperfK : Group.IsPerfect ↥K := by
    refine ⟨?_⟩
    rw [commutator_def]
    have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator]
      simp only [Subgroup.map_top, Subgroup.range_subtype]
      exact hKperf
    exact htop
  haveI : Group.IsPerfect ↥K := hperfK
  haveI : IsSimpleGroup ↥K := hK
  have hZ : Subgroup.center ↥K = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥K)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (⟨(k : Ω), hKL k.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← ker_piL e, MonoidHom.mem_ker]
      exact hk
    have hcent : (k : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply Subtype.ext
      exact congrArg (fun x : ↥L => (x : Ω))
        (Subgroup.mem_center_iff.mp hk' ⟨(k' : Ω), hKL k'.2⟩)
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hcent
  have hrange : f.range = imL e K := by
    ext x
    rw [MonoidHom.mem_range, show imL e K = (K.subgroupOf L).map (piL e) from rfl,
      Subgroup.mem_map]
    exact ⟨fun ⟨k, hk⟩ => ⟨⟨k, hKL k.2⟩, k.2, hk⟩,
      fun ⟨l, hl, hl'⟩ => ⟨⟨l, hl⟩, hl'⟩⟩
  have hcard : Nat.card f.range = Nat.card ↥K := by
    rw [← Subgroup.map_top f, Subgroup.card_map_of_injective (K := ⊤) hf]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [← hrange, hcard]

theorem le_imL_centralizer [Finite Ω] [L.Normal]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {b : Ω} {F : Subgroup S6}
    (hF : F ≤ fixSubgroup (theta L e b)) (hperf : ⁅F, F⁆ = F) :
    F ≤ imL e (L ⊓ Subgroup.centralizer ({b} : Set Ω)) := by
  have hker : (piL e).ker ≤ Subgroup.center ↥L := (ker_piL e).le
  have hαβ : ∀ k : ↥L, piL e (MulAut.conjNormal (H := L) b k) = theta L e b (piL e k) := by
    intro k
    rw [theta_piL]
    congr 1
  have h := CFSG.HardMathSupport.Solomon.Coordinator.le_map_fixSubgroup_of_perfect
    (piL e) hker (MulAut.conjNormal (H := L) b) (theta L e b) hαβ
    (piL_surjective e) hF hperf
  have hfix : fixSubgroup (MulAut.conjNormal (H := L) b) =
      (L ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf L := by
    ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      have hk' : b * (k : Ω) * b⁻¹ = (k : Ω) := by
        have h := congrArg (fun x : ↥L => (x : Ω)) hk
        rwa [MulAut.conjNormal_apply] at h
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (show b * (k : Ω) = (k : Ω) * b from by
        calc b * (k : Ω) = (b * (k : Ω) * b⁻¹) * b := by group
          _ = (k : Ω) * b := by rw [hk']).symm
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hkb : (k : Ω) * b = b * (k : Ω) :=
        Subgroup.mem_centralizer_singleton_iff.mp hk
      calc b * (k : Ω) * b⁻¹ = (b * (k : Ω)) * b⁻¹ := rfl
        _ = ((k : Ω) * b) * b⁻¹ := by rw [hkb.symm]
        _ = (k : Ω) := by group
  rw [hfix] at h
  exact h

end Image

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
