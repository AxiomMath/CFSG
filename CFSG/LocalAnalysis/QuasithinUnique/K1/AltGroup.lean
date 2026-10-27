module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.AltFinite
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient

public section

namespace CFSG.QuasithinUnique.K1.Alt

open CFSG.Open CFSG.QuasithinUnique.RankOneRecog CFSG.ComponentClassification.PerfectAutomorphisms

private abbrev AltGrp (n : ℕ) := alternatingGroup (Fin n)

private theorem exists_central_adjust {Λ : Type*} [Group Λ] [Finite Λ] (α : Λ ≃* Λ)
    (hα : ∀ x, α (α x) = x) {T : Subgroup Λ} (hT : ∀ t ∈ T, α t = t)
    (hZ : ∀ z ∈ Subgroup.center Λ, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ T)
    {g₀ τ z₀ : Λ} (hτ : τ ∈ T) (hz₀ : z₀ ∈ Subgroup.center Λ)
    (h : (α g₀)⁻¹ * g₀ = τ * z₀) :
    ∃ z ∈ Subgroup.center Λ, (α (g₀ * z))⁻¹ * (g₀ * z) ∈ T := by
  have hc : α ((α g₀)⁻¹ * g₀) = ((α g₀)⁻¹ * g₀)⁻¹ := by
    rw [map_mul, map_inv, hα]; group
  rw [h, map_mul, hT τ hτ] at hc
  have hzc : ∀ (k : ℕ) (x : Λ), z₀ ^ k * x = x * z₀ ^ k := fun k x =>
    (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz₀ k) x).symm
  have hα1 : α z₀ = (τ ^ 2 * z₀)⁻¹ := by
    have h2 : τ * α z₀ = z₀⁻¹ * τ⁻¹ := by rw [hc]; group
    have h3 : α z₀ = τ⁻¹ * (z₀⁻¹ * τ⁻¹) := by
      calc α z₀ = τ⁻¹ * (τ * α z₀) := by group
        _ = τ⁻¹ * (z₀⁻¹ * τ⁻¹) := by rw [h2]
    rw [h3]
    have h4 : z₀⁻¹ * τ⁻¹ = τ⁻¹ * z₀⁻¹ := by
      have := hzc 1 τ
      simp only [pow_one] at this
      calc z₀⁻¹ * τ⁻¹ = (τ * z₀)⁻¹ := by group
        _ = (z₀ * τ)⁻¹ := by rw [this]
        _ = τ⁻¹ * z₀⁻¹ := by group
    rw [h4]
    have h5 : (τ ^ 2 * z₀)⁻¹ = z₀⁻¹ * (τ ^ 2)⁻¹ := by group
    rw [h5]
    have := hzc 1 (τ ^ 2)
    simp only [pow_one] at this
    calc τ⁻¹ * (τ⁻¹ * z₀⁻¹) = (τ ^ 2)⁻¹ * z₀⁻¹ := by group
      _ = z₀⁻¹ * (τ ^ 2)⁻¹ := by
        have h6 : (z₀ * τ ^ 2)⁻¹ = (τ ^ 2 * z₀)⁻¹ := by rw [this]
        simpa [mul_inv_rev] using h6
  obtain ⟨s, m, hm, hord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (isOfFinOrder_of_finite z₀).orderOf_pos.ne'
  obtain ⟨j, rfl⟩ := hm
  refine ⟨z₀ ^ j, Subgroup.pow_mem _ hz₀ j, ?_⟩
  have hαz : α (z₀ ^ j) = ((τ ^ 2 * z₀) ^ j)⁻¹ := by
    rw [map_pow, hα1, inv_pow]
  have hcomm : Commute (τ ^ 2) z₀ := by
    have := hzc 1 (τ ^ 2)
    simp only [pow_one] at this
    exact this.symm
  have hexp : (α (g₀ * z₀ ^ j))⁻¹ * (g₀ * z₀ ^ j) = τ ^ (2 * j + 1) * z₀ ^ (2 * j + 1) := by
    have e1 : (α (g₀ * z₀ ^ j))⁻¹ * (g₀ * z₀ ^ j) =
        (α (z₀ ^ j))⁻¹ * ((α g₀)⁻¹ * g₀) * z₀ ^ j := by
      rw [map_mul, mul_inv_rev]; group
    rw [e1, h, hαz, inv_inv, hcomm.mul_pow]
    have e2 : z₀ ^ j * (τ * z₀) = (τ * z₀) * z₀ ^ j := hzc j (τ * z₀)
    calc (τ ^ 2) ^ j * z₀ ^ j * (τ * z₀) * z₀ ^ j
        = (τ ^ 2) ^ j * (z₀ ^ j * (τ * z₀)) * z₀ ^ j := by group
      _ = (τ ^ 2) ^ j * ((τ * z₀) * z₀ ^ j) * z₀ ^ j := by rw [e2]
      _ = τ ^ (2 * j + 1) * z₀ ^ (2 * j + 1) := by group
  rw [hexp]
  refine T.mul_mem (T.pow_mem hτ _) (hZ _ (Subgroup.pow_mem _ hz₀ _) ⟨s, ?_⟩)
  rw [← pow_mul]
  have : (2 * j + 1) * 2 ^ s = orderOf z₀ := by rw [hord]; ring
  rw [this, pow_orderOf_eq_one]


section PartI

variable {G : Type} [Group G] [Finite G]

private theorem false_of_qlevel_core {H S U L : Subgroup G} (hD : StrongClosureComponent H S U L)
    {n : ℕ} {R : Subgroup (AltGrp n)} (hq : QLevelFalse n R)
    (Tsyl : Sylow 2 L) (hT : (Tsyl : Subgroup L).map L.subtype = S ⊓ L)
    (φ : (L ⧸ Subgroup.center L) ≃* AltGrp n)
    (hRP : R ≤ (Tsyl : Subgroup L).map
      ((φ : (L ⧸ Subgroup.center L) →* AltGrp n).comp (QuotientGroup.mk' (Subgroup.center L))))
    {w : G} (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hwL : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) : False := by
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := hD.normalizes hwU
  have hw2 : w ^ 2 = 1 := hD.elem.2 w hwU
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hD.perfect
  set π : L →* AltGrp n :=
    (φ : (L ⧸ Subgroup.center L) →* AltGrp n).comp (QuotientGroup.mk' (Subgroup.center L))
    with hπdef
  have hπsurj : Function.Surjective π := fun x => by
    obtain ⟨q, rfl⟩ := φ.surjective x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    exact ⟨g, rfl⟩
  have hπker : ∀ x : L, π x = 1 ↔ x ∈ Subgroup.center L := fun x => by
    have : π x = φ (QuotientGroup.mk' (Subgroup.center L) x) := rfl
    rw [this, map_eq_one_iff φ φ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hTS : ∀ t : L, t ∈ Tsyl → (t : G) ∈ S := fun t ht => by
    have : (t : G) ∈ (Tsyl : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ ht
    rw [hT] at this
    exact this.1
  have hST : ∀ a : L, (a : G) ∈ S → a ∈ Tsyl := fun a ha => by
    have : (a : G) ∈ S ⊓ (L : Subgroup G) := ⟨ha, a.2⟩
    rw [← hT] at this
    obtain ⟨t, ht, hta⟩ := this
    have : t = a := Subtype.ext hta
    rwa [this] at ht
  set α : L ≃* L := conjAutOfNormalizer L hwN with hαdef
  have hαc : ∀ y : L, ((α y : L) : G) = w⁻¹ * y * w := fun y => rfl
  have hα2 : ∀ x : L, α (α x) = x := fun x => by
    apply Subtype.ext
    rw [hαc, hαc, hwinv]
    calc w * (w * (x : G) * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hww]; simp
  have hαT : ∀ t ∈ (Tsyl : Subgroup L), α t = t := fun t ht => by
    apply Subtype.ext
    rw [hαc]
    have h1 : (t : G) * w = w * (t : G) := Subgroup.mem_centralizer_iff.mp hwS (t : G) (hTS t ht)
    calc w⁻¹ * (t : G) * w = w⁻¹ * (w * (t : G)) := by rw [mul_assoc, h1]
      _ = t := by group
  have hZ : ∀ z ∈ Subgroup.center L, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ (Tsyl : Subgroup L) := by
    rintro z hz ⟨k, hk⟩
    have hnorm : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
    have hp : IsPGroup 2 (Subgroup.zpowers z) := by
      intro g
      refine ⟨k, Subtype.ext ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
      have : (g : L) ^ 2 ^ k = 1 := by
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
      simpa using this
    exact IsPGroup.le_sylow_of_normal (N := Subgroup.zpowers z) hp Tsyl (Subgroup.mem_zpowers z)
  set βQ : MulAut (L ⧸ Subgroup.center L) := onCenterQuotient α with hβQdef
  have hβQ : ∀ x : L, βQ (QuotientGroup.mk' (Subgroup.center L) x) =
      QuotientGroup.mk' (Subgroup.center L) (α x) := fun x => onCenterQuotient_apply_mk α x
  set β : MulAut (AltGrp n) := φ.symm.trans (βQ.trans φ) with hβdef
  have hβπ : ∀ x : L, β (π x) = π (α x) := fun x => by
    show φ (βQ (φ.symm (φ (QuotientGroup.mk' (Subgroup.center L) x)))) =
      φ (QuotientGroup.mk' (Subgroup.center L) (α x))
    rw [MulEquiv.symm_apply_apply, hβQ]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hwL
    have hβQ1 : βQ = 1 := by
      refine MulEquiv.ext fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
      have h1 : β (π x) = π x := by rw [h]; rfl
      rw [hβπ] at h1
      have h2 : QuotientGroup.mk' (Subgroup.center L) (α x) =
          QuotientGroup.mk' (Subgroup.center L) x := φ.injective h1
      rw [hβQ, h2]
      rfl
    have hα1 : α = 1 := onCenterQuotient_eq_one_imp α hβQ1
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] 
    have h3 : α ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hα1]; rfl
    have h4 := congrArg Subtype.val h3
    rw [hαc] at h4
    show x * w = w * x
    calc x * w = w * (w⁻¹ * x * w) := by group
      _ = w * x := by rw [h4]
  set P : Subgroup (AltGrp n) := (Tsyl : Subgroup L).map π with hPdef
  have hβP : ∀ p ∈ P, β p = p := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hβπ, hαT t ht]
  set V : Subgroup (AltGrp n) := (U.subgroupOf L).map π with hVdef
  have hUsub : ∀ a : L, a ∈ U.subgroupOf L → (a : G) ∈ U := fun a ha => ha
  have hVP : V ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map_of_mem π (hST a (hD.le_S (hUsub a ha)))
  have hVe : IsElemAbelian 2 V := by
    have hU' : IsElemAbelian 2 (U.subgroupOf L) := isElemAbelian_subgroupOf hD.elem
    refine ⟨IsMulCommutative.mk (Std.Commutative.mk fun a b => ?_), ?_⟩
    · obtain ⟨a', ha', haa⟩ := a.2
      obtain ⟨b', hb', hbb⟩ := b.2
      apply Subtype.ext
      have h1 := hU'.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      have h2 : a' * b' = b' * a' := congrArg Subtype.val h1
      show (a : AltGrp n) * (b : AltGrp n) = (b : AltGrp n) * (a : AltGrp n)
      rw [← haa, ← hbb, ← map_mul, ← map_mul, h2]
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow, hU'.2 a' ha', map_one]
  have hVcl : ∀ v ∈ V, ∀ x : AltGrp n, x⁻¹ * v * x ∈ P → x⁻¹ * v * x ∈ V := by
    rintro v ⟨a, ha, rfl⟩ x hx
    obtain ⟨g, rfl⟩ := hπsurj x
    obtain ⟨t, htT, hty⟩ := hx
    have hπy : π (g⁻¹ * a * g) = (π g)⁻¹ * π a * π g := by
      rw [map_mul, map_mul, map_inv]
    have hz : t⁻¹ * (g⁻¹ * a * g) ∈ Subgroup.center L := by
      rw [← hπker, map_mul, map_inv, hty, hπy]
      group
    have ha2 : a ^ 2 = 1 :=
      Subtype.ext (by simpa using hD.elem.2 (a : G) (hUsub a ha))
    have hy2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [← pow_two, ha2]; group
    set z : L := t⁻¹ * (g⁻¹ * a * g) with hzdef
    have hyz : g⁻¹ * a * g = t * z := by rw [hzdef]; group
    have hzt : t * z = z * t := Subgroup.mem_center_iff.mp hz t
    have hz2 : z * z = (t * t)⁻¹ := by
      have h1 : (t * t) * (z * z) = 1 := by
        calc (t * t) * (z * z) = (t * z) * (t * z) := by
              calc (t * t) * (z * z) = t * (t * z) * z := by group
                _ = t * (z * t) * z := by rw [hzt]
                _ = (t * z) * (t * z) := by group
          _ = 1 := by rw [← hyz]; exact hy2
      exact eq_inv_of_mul_eq_one_right h1
    obtain ⟨k, hk⟩ := Tsyl.isPGroup' (⟨t, htT⟩ : Tsyl)
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hzk : z ^ 2 ^ (k + 1) = 1 := by
      calc z ^ 2 ^ (k + 1) = (z * z) ^ 2 ^ k := by
            rw [pow_succ', pow_mul, pow_two]
        _ = ((t * t)⁻¹) ^ 2 ^ k := by rw [hz2]
        _ = 1 := by
          rw [inv_pow, ← pow_two, ← pow_mul, mul_comm, pow_mul, htk]
          simp
    have hzT : z ∈ (Tsyl : Subgroup L) := hZ z hz ⟨k + 1, hzk⟩
    have hyT : g⁻¹ * a * g ∈ Tsyl := by
      rw [hyz]; exact Tsyl.mul_mem htT hzT
    have hyS : (((g⁻¹ * a * g : L)) : G) ∈ S := hTS _ hyT
    have hyU : (((g⁻¹ * a * g : L)) : G) ∈ U := by
      have h5 := hD.closed (a : G) (hUsub a ha) (g : G) (hD.le_H g.2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hyS ⊢
      exact h5 hyS
    rw [← hπy]
    exact Subgroup.mem_map_of_mem π hyU
  have hTC : ∀ x : AltGrp n, (β x)⁻¹ * x ∈ P → (β x)⁻¹ * x ∈ V := by
    intro x hx
    obtain ⟨g₀, rfl⟩ := hπsurj x
    rw [hβπ] at hx
    obtain ⟨τ, hτ, hτe⟩ := hx
    have hz₀ : τ⁻¹ * ((α g₀)⁻¹ * g₀) ∈ Subgroup.center L := by
      rw [← hπker, map_mul, map_inv, hτe, map_mul, map_inv]
      group
    obtain ⟨z, hz, hzT⟩ := exists_central_adjust (g₀ := g₀) α hα2 hαT hZ hτ hz₀ (by group)
    have hπz : π z = 1 := (hπker z).mpr hz
    have hπg : π (g₀ * z) = π g₀ := by rw [map_mul, hπz, mul_one]
    have hcG : (((α (g₀ * z))⁻¹ * (g₀ * z) : L) : G) =
        w⁻¹ * ((g₀ * z : L) : G)⁻¹ * w * ((g₀ * z : L) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαc]
      group
    have hcS : (((α (g₀ * z))⁻¹ * (g₀ * z) : L) : G) ∈ S := hTS _ hzT
    have hwcS : ((g₀ * z : L) : G)⁻¹ * w * ((g₀ * z : L) : G) ∈ S := by
      have h1 : ((g₀ * z : L) : G)⁻¹ * w * ((g₀ * z : L) : G) =
          w * (((α (g₀ * z))⁻¹ * (g₀ * z) : L) : G) := by rw [hcG]; group
      rw [h1]
      exact S.mul_mem (hD.le_S hwU) hcS
    have hwcU := hD.closed w hwU ((g₀ * z : L) : G) (hD.le_H (g₀ * z).2) hwcS
    have hcU : (((α (g₀ * z))⁻¹ * (g₀ * z) : L) : G) ∈ U := by
      have h1 : (((α (g₀ * z))⁻¹ * (g₀ * z) : L) : G) =
          w⁻¹ * (((g₀ * z : L) : G)⁻¹ * w * ((g₀ * z : L) : G)) := by rw [hcG]; group
      rw [h1]
      exact U.mul_mem (U.inv_mem hwU) hwcU
    have hπc : π ((α (g₀ * z))⁻¹ * (g₀ * z)) = (β (π g₀))⁻¹ * π g₀ := by
      rw [map_mul, map_inv, ← hβπ, hπg]
    rw [← hπc]
    exact Subgroup.mem_map_of_mem π hcU
  exact hq P V β hRP hβ1 hβP hVP hVe hVcl hTC


private theorem exists_iso_sylow_le {L : Subgroup G} (Tsyl : Sylow 2 L) {n : ℕ} {R : Subgroup (AltGrp n)}
    (hR : IsPGroup 2 R) (φ : (L ⧸ Subgroup.center L) ≃* AltGrp n) :
    ∃ φ' : (L ⧸ Subgroup.center L) ≃* AltGrp n, R ≤ (Tsyl : Subgroup L).map
      ((φ' : (L ⧸ Subgroup.center L) →* AltGrp n).comp
        (QuotientGroup.mk' (Subgroup.center L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π₀ : L →* AltGrp n :=
    (φ : (L ⧸ Subgroup.center L) →* AltGrp n).comp (QuotientGroup.mk' (Subgroup.center L))
    with hπ₀
  have hπ₀surj : Function.Surjective π₀ := fun x => by
    obtain ⟨q, rfl⟩ := φ.surjective x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    exact ⟨g, rfl⟩
  have hP₀p : IsPGroup 2 ((Tsyl : Subgroup L).map π₀) := Tsyl.isPGroup'.map π₀
  have hP₀i : ¬ 2 ∣ ((Tsyl : Subgroup L).map π₀).index := by
    intro h2
    have h1 : ((Tsyl : Subgroup L).map π₀).index = (((Tsyl : Subgroup L).map π₀).comap π₀).index :=
      (Subgroup.index_comap_of_surjective _ hπ₀surj).symm
    have h3 : (((Tsyl : Subgroup L).map π₀).comap π₀).index ∣ (Tsyl : Subgroup L).index :=
      Subgroup.index_dvd_of_le (Subgroup.le_comap_map _ _)
    exact Tsyl.not_dvd_index (h2.trans (h1 ▸ h3))
  let P₀s : Sylow 2 (AltGrp n) := hP₀p.toSylow hP₀i
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (AltGrp n) P₀s Q
  have hmem : ∀ x : AltGrp n, x ∈ (Q : Subgroup (AltGrp n)) ↔
      g⁻¹ * x * g ∈ (P₀s : Subgroup (AltGrp n)) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine ⟨φ.trans (MulAut.conj g), fun r hr => ?_⟩
  have h1 : g⁻¹ * r * g ∈ ((Tsyl : Subgroup L).map π₀) := (hmem r).mp (hRQ hr)
  obtain ⟨t, ht, hte⟩ := h1
  exact ⟨t, ht, by
    show (MulAut.conj g) (φ (QuotientGroup.mk' (Subgroup.center L) t)) = r
    have : φ (QuotientGroup.mk' (Subgroup.center L) t) = π₀ t := rfl
    rw [this, hte, MulAut.conj_apply]
    group⟩

theorem false_of_qlevel {H S U L : Subgroup G} (hD : StrongClosureComponent H S U L)
    {n : ℕ} {R : Subgroup (alternatingGroup (Fin n))} (hR : IsPGroup 2 R)
    (hq : QLevelFalse n R)
    (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) {w : G} (hwU : w ∈ U)
    (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hwL : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) : False := by
  obtain ⟨Tsyl, hT⟩ := exists_sylow_inf_of_subnormal hD.sylow hD.le_H hD.subnormal
  obtain ⟨φ', hφ'⟩ := exists_iso_sylow_le Tsyl hR φ
  exact false_of_qlevel_core hD hq Tsyl hT φ' hφ' hwU hwS hwL

end PartI


end CFSG.QuasithinUnique.K1.Alt
