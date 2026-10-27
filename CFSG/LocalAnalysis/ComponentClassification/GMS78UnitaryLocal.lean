module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicUnitary
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BenderAction
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G]

theorem quotAutHom_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    quotAutHom L ⟨l, le_normalizer hl⟩ = MulAut.conj (QuotientGroup.mk' (center L) ⟨l, hl⟩) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
  rw [quotAutHom_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem quotAutHom_of_mem_centralizer {L : Subgroup G} {k : G}
    (hk : k ∈ centralizer (L : Set G)) (hkN : k ∈ normalizer (L : Set G)) :
    quotAutHom L ⟨k, hkN⟩ = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
  rw [quotAutHom_apply_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe, ← mem_centralizer_iff.mp hk x x.2, mul_inv_cancel_right]

@[expose] noncomputable def sylowProj {L P : Subgroup G} (hPL : P ≤ L) : P →* rankTwoQuot L :=
  (QuotientGroup.mk' (center L)).comp (Subgroup.inclusion hPL)

theorem sylowProj_apply {L P : Subgroup G} (hPL : P ≤ L) (x : P) :
    sylowProj hPL x = QuotientGroup.mk' (center L) ⟨x, hPL x.2⟩ := rfl

variable [Finite G]

theorem sylowProj_injective {L P : Subgroup G} (hZ : Odd (Nat.card (center L)))
    (hP : IsPGroup 2 P) (hPL : P ≤ L) : Function.Injective (sylowProj hPL) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : (⟨x, hPL x.2⟩ : L) ∈ center L := (QuotientGroup.eq_one_iff _).mp hx
  have hbot : P.subgroupOf L ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L)
      (hP.comap_subtype.to_inf_left) hZ inf_le_right
  have h1 : (⟨x, hPL x.2⟩ : L) ∈ P.subgroupOf L ⊓ center L := mem_inf.mpr ⟨x.2, hxZ⟩
  rw [hbot, mem_bot] at h1
  have h2 : (x : G) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem exists_sylow_range {L P : Subgroup G} (hP : IsSylowOf 2 P L) :
    ∃ R : Sylow 2 (rankTwoQuot L), (sylowProj hP.le).range = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  refine ⟨Q.mapSurjective (f := QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _),
    ?_⟩
  ext y
  rw [Sylow.coe_mapSurjective, MonoidHom.mem_range, mem_map, hQ]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hP.le x.2⟩, x.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

omit [Finite G] in
theorem quotAutHom_sylowProj {L P : Subgroup G} (hPL : P ≤ L) {x : G}
    (hxN : x ∈ normalizer (L : Set G)) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) (p : P) :
    quotAutHom L ⟨x, hxN⟩ (sylowProj hPL p) = sylowProj hPL ⟨x * p * x⁻¹, hxP p p.2⟩ := by
  rw [sylowProj_apply, sylowProj_apply, quotAutHom_apply_mk]
  congr 1

theorem mem_center_iff_sylowProj {L P : Subgroup G} (hZ : Odd (Nat.card (center L)))
    (hP : IsSylowOf 2 P L) {R : Sylow 2 (rankTwoQuot L)} (hR : (sylowProj hP.le).range = R)
    (p : P) : (p : G) ∈ P ⊓ centralizer (P : Set G) ↔
      sylowProj hP.le p ∈ sylowCenter (R : Subgroup (rankTwoQuot L)) := by
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  rw [mem_sylowCenter, ← hR]
  constructor
  · rintro ⟨-, hpc⟩
    refine ⟨⟨p, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hpc y y.2)
  · rintro ⟨-, hc⟩
    refine ⟨p.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := hc (sylowProj hP.le ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have h2 : ((⟨y, hy⟩ * p : P) : G) = ((p * ⟨y, hy⟩ : P) : G) := congrArg Subtype.val (hinj h1)
    exact h2

theorem sylow_of_psu3 {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) (hP : IsSylowOf 2 P L) :
    Nat.card P = (2 ^ f) ^ 3 ∧ Nat.card (P ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ f ∧
      (∀ a ∈ P ⊓ centralizer (P : Set G), a ^ 2 = 1) ∧
      (∀ x ∈ P, x ^ 2 = 1 → x ∈ P ⊓ centralizer (P : Set G)) ∧
      (∀ x ∈ P, x ^ 2 ∈ P ⊓ centralizer (P : Set G)) ∧
      Nat.card (commutator P) = 2 ^ f := by
  have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  set ρ := sylowProj hP.le with hρ
  have hcen := mem_center_iff_sylowProj hZ hP hR
  obtain ⟨hRcard, hZcard, hinv, hsq, hcomm⟩ := sylow_psu3 hf e R
  obtain ⟨-, hZ2, -, -⟩ :=
    benderBorel_sylowCenter (Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e) R
  let ι : P ≃* (R : Subgroup (rankTwoQuot L)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hR)
  have hρR : ∀ p, ρ p ∈ (R : Subgroup (rankTwoQuot L)) := fun p => hR ▸ ⟨p, rfl⟩
  refine ⟨?_, ?_, fun a ha => ?_, fun x hx hx2 => ?_, fun x hx => ?_, ?_⟩
  · rw [Nat.card_congr ι.toEquiv, hRcard]
  · rw [← hZcard]
    refine Nat.card_congr (Equiv.ofBijective
      (fun a => ⟨ρ ⟨a, a.2.1⟩, (hcen ⟨a, a.2.1⟩).mp a.2⟩) ⟨fun a b hab => ?_, fun z => ?_⟩)
    · have h1 := hinj (congrArg Subtype.val hab)
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext h2
    · have hzR : (z : rankTwoQuot L) ∈ ρ.range := by
        rw [hR]
        exact sylowCenter_le _ z.2
      obtain ⟨p, hp⟩ := hzR
      refine ⟨⟨p, (hcen p).mpr (hp ▸ z.2)⟩, Subtype.ext ?_⟩
      exact hp
  · have h1 := hZ2 _ ((hcen ⟨a, ha.1⟩).mp ha)
    rw [← map_pow] at h1
    have h2 := congrArg Subtype.val (hinj (h1.trans (map_one ρ).symm))
    simpa using h2
  · have h1 : ρ ⟨x, hx⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : P) ^ 2 = 1 := Subtype.ext hx2
      rw [this, map_one]
    exact (hcen ⟨x, hx⟩).mpr (hinv _ (hρR _) h1)
  · have h1 := hsq _ (hρR ⟨x, hx⟩)
    rw [← map_pow] at h1
    exact (hcen _).mpr h1
  · rw [card_commutator_congr ι, hcomm]

theorem outer_inv_of_psu3 {L P : Subgroup G} (hLp : commutator L = ⊤)
    (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    (hP : IsSylowOf 2 P L) {w : G} (hwN : w ∈ normalizer (L : Set G)) (hww : w * w = 1)
    (hwLK : w ∉ L ⊔ centralizer (L : Set G)) (hwP : ∀ p ∈ P, w * p * w⁻¹ ∈ P) :
    (∀ a ∈ P ⊓ centralizer (P : Set G), w * a = a * w) ∧
      ∀ x ∈ P, w * x = x * w → x ∈ P ⊓ centralizer (P : Set G) := by
  have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  set ρ := sylowProj hP.le with hρ
  have hcen := mem_center_iff_sylowProj hZ hP hR
  set n : normalizer (L : Set G) := ⟨w, hwN⟩ with hn
  set α := quotAutHom L n with hαdef
  have hαα : α * α = 1 := by
    rw [hαdef, ← map_mul]
    have : n * n = 1 := Subtype.ext hww
    rw [this, map_one]
  have hα : ¬ ∃ y, α = MulAut.conj y := by
    rintro ⟨y, hy⟩
    exact hwLK (mem_sup_centralizer_of_quotAut_mem_inner hLp hwN ⟨y, hy.symm⟩)
  have hαρ : ∀ p : P, α (ρ p) = ρ ⟨w * p * w⁻¹, hwP p p.2⟩ := fun p =>
    quotAutHom_sylowProj hP.le hwN hwP p
  have hαR : ∀ r ∈ (R : Subgroup (rankTwoQuot L)), α r ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro r hr
    rw [← hR] at hr ⊢
    obtain ⟨p, rfl⟩ := hr
    rw [hαρ]
    exact ⟨_, rfl⟩
  obtain ⟨hZf, hfix⟩ := inv_fix_of_not_inner_psu3 hf e α hαα hα R hαR
  refine ⟨fun a ha => ?_, fun x hx hwx => ?_⟩
  · have h1 := hZf _ ((hcen ⟨a, ha.1⟩).mp ha)
    rw [hαρ] at h1
    have h2 : w * a * w⁻¹ = a := congrArg Subtype.val (hinj h1)
    calc w * a = w * a * w⁻¹ * w := by group
      _ = a * w := by rw [h2]
  · have h1 : α (ρ ⟨x, hx⟩) = ρ ⟨x, hx⟩ := by
      rw [hαρ]
      congr 1
      apply Subtype.ext
      show w * x * w⁻¹ = x
      rw [hwx, mul_inv_cancel_right]
    have hxR : ρ ⟨x, hx⟩ ∈ (R : Subgroup (rankTwoQuot L)) := hR ▸ ⟨⟨x, hx⟩, rfl⟩
    exact (hcen ⟨x, hx⟩).mpr (hfix _ hxR h1)

theorem centralizer_le_of_psu3 {L P : Subgroup G} (hLp : commutator L = ⊤)
    (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    (hP : IsSylowOf 2 P L) {x : G} (hxN : x ∈ normalizer (L : Set G))
    (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) {n : ℕ} (hxn : x ^ 2 ^ n = 1)
    (hxA : ∀ a ∈ P ⊓ centralizer (P : Set G), x * a = a * x)
    (hxLK : x ∉ L ⊔ centralizer (L : Set G))
    (hx2 : ∃ a ∈ P ⊓ centralizer (P : Set G), ∃ k ∈ centralizer (L : Set G), x ^ 2 = a * k) :
    ∀ y ∈ P, x * y = y * x → y ∈ P ⊓ centralizer (P : Set G) := by
  have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  set ρ := sylowProj hP.le with hρ
  have hcen := mem_center_iff_sylowProj hZ hP hR
  set m : normalizer (L : Set G) := ⟨x, hxN⟩ with hm
  set α := quotAutHom L m with hαdef
  have hαρ : ∀ p : P, α (ρ p) = ρ ⟨x * p * x⁻¹, hxP p p.2⟩ := fun p =>
    quotAutHom_sylowProj hP.le hxN hxP p
  have hαR : ∀ r ∈ (R : Subgroup (rankTwoQuot L)), α r ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro r hr
    rw [← hR] at hr ⊢
    obtain ⟨p, rfl⟩ := hr
    rw [hαρ]
    exact ⟨_, rfl⟩
  have hfixρ : ∀ p : P, x * p = p * x → α (ρ p) = ρ p := by
    intro p hp
    rw [hαρ]
    congr 1
    apply Subtype.ext
    show x * p * x⁻¹ = p
    rw [hp, mul_inv_cancel_right]
  have hαZ : ∀ z ∈ sylowCenter (R : Subgroup (rankTwoQuot L)), α z = z := by
    intro z hz
    have hzR : z ∈ ρ.range := by
      rw [hR]
      exact sylowCenter_le _ hz
    obtain ⟨p, rfl⟩ := hzR
    exact hfixρ p (hxA p ((hcen p).mpr hz))
  have hαpow : α ^ 2 ^ n = 1 := by
    rw [hαdef, ← map_pow]
    have : m ^ 2 ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this, map_one]
  have hout : ∀ s ∈ (R : Subgroup (rankTwoQuot L)), α ≠ MulAut.conj s := fun s _ h =>
    hxLK (mem_sup_centralizer_of_quotAut_mem_inner hLp hxN ⟨s, h.symm⟩)
  obtain ⟨-, hctrl, -⟩ := autControlAt_of_mulEquiv_psu3 hf e R α hαR hαZ ⟨n, hαpow⟩ hout
  obtain ⟨a, ha, k, hk, hxak⟩ := hx2
  have hkN : k ∈ normalizer (L : Set G) := centralizer_le_normalizer L hk
  have hα2 : α ^ 2 = MulAut.conj (ρ ⟨a, ha.1⟩) := by
    have h1 : m ^ 2 = ⟨a, le_normalizer (hP.le ha.1)⟩ * ⟨k, hkN⟩ :=
      Subtype.ext (by simpa [hm] using hxak)
    rw [hαdef, ← map_pow, h1, map_mul, quotAutHom_of_mem (hP.le ha.1),
      quotAutHom_of_mem_centralizer hk hkN, mul_one]
    rfl
  have hfix := hctrl ⟨ρ ⟨a, ha.1⟩, (hcen ⟨a, ha.1⟩).mp ha, hα2⟩
  intro y hy hxy
  have hyR : ρ ⟨y, hy⟩ ∈ (R : Subgroup (rankTwoQuot L)) := hR ▸ ⟨⟨y, hy⟩, rfl⟩
  exact (hcen ⟨y, hy⟩).mpr (hfix _ hyR (hfixρ ⟨y, hy⟩ hxy))

theorem mul_mem_sup_of_psu3 {L P : Subgroup G} (hLp : commutator L = ⊤)
    (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    (hP : IsSylowOf 2 P L) {E : Subgroup G} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (L : Set G)) (hEP : ∀ x ∈ E, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hEA : ∀ x ∈ E, ∀ a ∈ P ⊓ centralizer (P : Set G), x * a = a * x) (hPE : P ≤ E)
    {x₁ x₂ : G} (h₁ : x₁ ∈ E) (h₂ : x₂ ∈ E) (h₁LK : x₁ ∉ L ⊔ centralizer (L : Set G))
    (h₂LK : x₂ ∉ L ⊔ centralizer (L : Set G)) : x₁ * x₂ ∈ L ⊔ centralizer (L : Set G) := by
  have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hcen := mem_center_iff_sylowProj hZ hP hR
  set ρ := sylowProj hP.le with hρ
  let σ : E →* MulAut (rankTwoQuot L) := (quotAutHom L).comp (Subgroup.inclusion hEN)
  have hσ : ∀ x : E, σ x = quotAutHom L ⟨x, hEN x.2⟩ := fun _ => rfl
  have hσρ : ∀ (x : E) (p : P), σ x (ρ p) = ρ ⟨x * p * x⁻¹, hEP x x.2 p p.2⟩ := fun x p =>
    quotAutHom_sylowProj hP.le (hEN x.2) (hEP x x.2) p
  have hP2 : IsPGroup 2 σ.range := hE.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  have hPR : ∀ β ∈ σ.range, ∀ r ∈ (R : Subgroup (rankTwoQuot L)),
      β r ∈ (R : Subgroup (rankTwoQuot L)) := by
    rintro _ ⟨x, rfl⟩ r hr
    rw [← hR] at hr ⊢
    obtain ⟨p, rfl⟩ := hr
    rw [hσρ]
    exact ⟨_, rfl⟩
  have hPZ : ∀ β ∈ σ.range, ∀ z ∈ sylowCenter (R : Subgroup (rankTwoQuot L)), β z = z := by
    rintro _ ⟨x, rfl⟩ z hz
    have hzR : z ∈ ρ.range := by
      rw [hR]
      exact sylowCenter_le _ hz
    obtain ⟨p, rfl⟩ := hzR
    rw [hσρ]
    congr 1
    apply Subtype.ext
    show (x : G) * p * (x : G)⁻¹ = p
    rw [hEA x x.2 p ((hcen p).mpr hz), mul_inv_cancel_right]
  have hinn : ∀ r ∈ (R : Subgroup (rankTwoQuot L)), MulAut.conj r ∈ σ.range := by
    intro r hr
    rw [← hR] at hr
    obtain ⟨p, rfl⟩ := hr
    refine ⟨⟨p, hPE p.2⟩, ?_⟩
    rw [hσ]
    exact quotAutHom_of_mem (hP.le p.2)
  have hout : ∀ (x : E), (x : G) ∉ L ⊔ centralizer (L : Set G) →
      ∀ r ∈ (R : Subgroup (rankTwoQuot L)), σ x ≠ MulAut.conj r := fun x hx r _ h =>
    hx (mem_sup_centralizer_of_quotAut_mem_inner hLp (hEN x.2) ⟨r, h.symm⟩)
  obtain ⟨r, -, hr⟩ := outer_pair_psu3 hf e R σ.range hP2 hPR hPZ hinn ⟨⟨x₁, h₁⟩, rfl⟩
    ⟨⟨x₂, h₂⟩, rfl⟩ (hout ⟨x₁, h₁⟩ h₁LK) (hout ⟨x₂, h₂⟩ h₂LK)
  apply mem_sup_centralizer_of_quotAut_mem_inner hLp (mul_mem (hEN h₁) (hEN h₂))
  refine ⟨r, ?_⟩
  rw [← hr, ← map_mul]
  rfl

theorem card_le_of_psu3 {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {f : ℕ}
    (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) (hP : IsSylowOf 2 P L) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hTN : T ≤ normalizer (L : Set G))
    (hTP : ∀ x ∈ T, ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    Nat.card T ≤ (2 ^ f - 1) *
      Nat.card (T ⊓ centralizer ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G) :
        Subgroup G) := by
  have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
  have : Finite (rankTwoQuot L) := inferInstance
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  have hcen := mem_center_iff_sylowProj hZ hP hR
  set ρ := sylowProj hP.le with hρ
  have hB := Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
  let σ : T →* MulAut (rankTwoQuot L) := (quotAutHom L).comp (Subgroup.inclusion hTN)
  have hσρ : ∀ (x : T) (p : P), σ x (ρ p) = ρ ⟨x * p * x⁻¹, hTP x x.2 p p.2⟩ := fun x p =>
    quotAutHom_sylowProj hP.le (hTN x.2) (hTP x x.2) p
  have hσR : ∀ x : T, ∀ r ∈ (R : Subgroup (rankTwoQuot L)),
      σ x r ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro x r hr
    rw [← hR] at hr ⊢
    obtain ⟨p, rfl⟩ := hr
    rw [hσρ]
    exact ⟨_, rfl⟩
  have h1 := card_le_mul_card_comap_fixing hB (by have := four_le_two_pow hf; omega) R hT σ hσR
  set A := P ⊓ centralizer (P : Set G) with hA
  have hcomap : (fixingSubgroup (MulAut (rankTwoQuot L))
      (sylowCenter (R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L))).comap σ =
      (T ⊓ centralizer (A : Set G)).subgroupOf T := by
    ext x
    rw [mem_comap, mem_fixingSubgroup_iff, mem_subgroupOf, mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h2 := hx (ρ ⟨a, ha.1⟩) ((hcen ⟨a, ha.1⟩).mp ha)
      change σ x (ρ ⟨a, ha.1⟩) = ρ ⟨a, ha.1⟩ at h2
      rw [hσρ] at h2
      have h3 : (x : G) * a * (x : G)⁻¹ = a := congrArg Subtype.val (hinj h2)
      calc a * x = x * a * (x : G)⁻¹ * x := by rw [h3]
        _ = x * a := by group
    · rintro ⟨-, hxc⟩ z hz
      have hzR : z ∈ ρ.range := by
        rw [hR]
        exact sylowCenter_le _ hz
      obtain ⟨p, rfl⟩ := hzR
      change σ x (ρ p) = ρ p
      rw [hσρ]
      congr 1
      apply Subtype.ext
      show (x : G) * p * (x : G)⁻¹ = p
      rw [← mem_centralizer_iff.mp hxc p ((hcen p).mpr hz), mul_inv_cancel_right]
  rw [hcomap] at h1
  have hle : T ⊓ centralizer (A : Set G) ≤ T := inf_le_left
  rwa [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h1

end CFSG.ComponentClassification.GMS78
