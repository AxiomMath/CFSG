module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Solomon

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

structure M10Cfg {K : Type} [Group K] (S D : Subgroup K) (z : K) : Prop where
  hz : orderOf z = 2
  hDC : D ≤ centralizer ({z} : Set K)
  hDn : ∀ c ∈ centralizer ({z} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D
  hDA : Nonempty (↥D ≃* alternatingGroup (Fin 6))
  hzD : z ∉ D
  hcard : Nat.card ↥(centralizer ({z} : Set K)) = 1440
  hinv : ∀ h ∈ centralizer ({z} : Set K), h * h ∈ zpowers z → h ∈ D ⊔ zpowers z
  hsq : ∀ h ∈ centralizer ({z} : Set K), h * h ∈ D ⊔ zpowers z
  hDS : D ≤ S

private theorem comm_of_mem_zpowers {G : Type*} [Group G] {c : G}
    (hc : ∀ g : G, g * c = c * g) {w : G} (hw : w ∈ Subgroup.zpowers c) (g : G) :
    w * g = g * w := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  exact ((show Commute c g from (hc g).symm).zpow_left m).eq

private theorem normal_zpowers_of_comm {G : Type*} [Group G] {c : G}
    (hc : ∀ g : G, g * c = c * g) : (Subgroup.zpowers c).Normal :=
  ⟨fun n hn g => by
    rw [← comm_of_mem_zpowers hc hn g, mul_inv_cancel_right]
    exact hn⟩

private theorem comm_self_of_alt6 {H : Type*} [Group H] (A : Subgroup H)
    (e : ↥A ≃* alternatingGroup (Fin 6)) : ⁅A, A⁆ = A := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
  haveI : Group.IsPerfect ↥A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.commutator_eq_self

open scoped commutatorElement in
private theorem commutator_sup_zpowers_le {G : Type*} [Group G] (A : Subgroup G) {c : G}
    (hc : ∀ g : G, g * c = c * g) : ⁅A ⊔ Subgroup.zpowers c, A ⊔ Subgroup.zpowers c⁆ ≤ A := by
  haveI := normal_zpowers_of_comm hc
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  obtain ⟨b, hb, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
  have hwc := comm_of_mem_zpowers hc hw
  have hvc := comm_of_mem_zpowers hc hv
  have key : ⁅a * w, b * v⁆ = a * b * a⁻¹ * b⁻¹ := by
    rw [commutatorElement_def]
    calc a * w * (b * v) * (a * w)⁻¹ * (b * v)⁻¹
        = a * (w * (b * v)) * (w⁻¹ * a⁻¹) * (v⁻¹ * b⁻¹) := by group
      _ = a * ((b * v) * w) * (w⁻¹ * a⁻¹) * (v⁻¹ * b⁻¹) := by rw [hwc (b * v)]
      _ = a * (b * v) * a⁻¹ * (v⁻¹ * b⁻¹) := by group
      _ = a * b * (v * a⁻¹) * (v⁻¹ * b⁻¹) := by group
      _ = a * b * (a⁻¹ * v) * (v⁻¹ * b⁻¹) := by rw [hvc a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [key]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

private theorem normal_of_alt6_index_two {G : Type*} [Group G] (A : Subgroup G) {c : G}
    (hc : ∀ g : G, g * c = c * g) (eA : ↥A ≃* alternatingGroup (Fin 6))
    (hidx : (A ⊔ Subgroup.zpowers c).index = 2) : A.Normal := by
  have hP : (A ⊔ Subgroup.zpowers c).Normal := Subgroup.normal_of_index_eq_two hidx
  haveI := normal_zpowers_of_comm hc
  have hle : ⁅A ⊔ Subgroup.zpowers c, A ⊔ Subgroup.zpowers c⁆ ≤ A :=
    commutator_sup_zpowers_le A hc
  have hge : A ≤ ⁅A ⊔ Subgroup.zpowers c, A ⊔ Subgroup.zpowers c⁆ := by
    calc A = ⁅A, A⁆ := (comm_self_of_alt6 A eA).symm
      _ ≤ ⁅A ⊔ Subgroup.zpowers c, A ⊔ Subgroup.zpowers c⁆ :=
        Subgroup.commutator_mono le_sup_left le_sup_left
  rw [← le_antisymm hle hge]
  exact Subgroup.commutator_normal _ _

private theorem eq_one_or_of_mem_zpowers {G : Type*} [Group G] {c : G} (hc2 : c ^ 2 = 1)
    (hc1 : c ≠ 1) {w : G} (hw : w ∈ Subgroup.zpowers c) : w = 1 ∨ w = c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h := zpow_mod_orderOf c m
  rw [hord] at h
  have hm : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hm with h0 | h1
  · exact Or.inl (by rw [← h, h0, zpow_zero])
  · exact Or.inr (by rw [← h, h1, zpow_one])

private theorem card_sup_zpowers_of_comm {G : Type*} [Group G] (A : Subgroup G) {c : G}
    (hc : ∀ g : G, g * c = c * g) (hc2 : c ^ 2 = 1) (hcA : c ∉ A) :
    Nat.card ↥(A ⊔ Subgroup.zpowers c) = 2 * Nat.card A := by
  haveI := normal_zpowers_of_comm hc
  have hc1 : c ≠ 1 := fun h => hcA (by rw [h]; exact A.one_mem)
  have hmem : ∀ (a : ↥A) (b : Bool), (a : G) * cond b c 1 ∈ A ⊔ Subgroup.zpowers c := by
    intro a b
    cases b
    · show (a : G) * 1 ∈ A ⊔ Subgroup.zpowers c
      rw [mul_one]
      exact Subgroup.mem_sup_left a.2
    · exact Subgroup.mul_mem_sup a.2 (Subgroup.mem_zpowers c)
  let f : ↥A × Bool → ↥(A ⊔ Subgroup.zpowers c) := fun p =>
    ⟨(p.1 : G) * cond p.2 c 1, hmem p.1 p.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * cond b c 1 = (a' : G) * cond b' c 1 := congrArg Subtype.val h
    cases b <;> cases b'
    · simp only [cond_false, mul_one] at h'
      exact Prod.ext (Subtype.ext h') rfl
    · exfalso
      simp only [cond_false, cond_true, mul_one] at h'
      apply hcA
      have hc' : c = (a' : G)⁻¹ * (a : G) := by rw [h']; group
      rw [hc']
      exact A.mul_mem (A.inv_mem a'.2) a.2
    · exfalso
      simp only [cond_false, cond_true, mul_one] at h'
      apply hcA
      have hc' : c = (a : G)⁻¹ * (a' : G) := by rw [← h']; group
      rw [hc']
      exact A.mul_mem (A.inv_mem a.2) a'.2
    · simp only [cond_true] at h'
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    rcases eq_one_or_of_mem_zpowers hc2 hc1 hw with h1 | h1
    · exact ⟨(⟨y, hy⟩, false), Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨y, hy⟩, true), Subtype.ext (by simp [f, h1])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

theorem m10_unpack {K : Type} [Group K] [Finite K] {z : K} (hz : orderOf z = 2)
    (hfc : fusionOddCore ↥(centralizer ({z} : Set K)) = ⊥)
    (hH : Fin76b.SolomonM10Hyp K z) :
    ∃ D : Subgroup K, D ≤ centralizer ({z} : Set K) ∧
      (∀ c ∈ centralizer ({z} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 6)) ∧ z ∉ D ∧
      Nat.card ↥(centralizer ({z} : Set K)) = 1440 ∧
      (∀ h ∈ centralizer ({z} : Set K), h * h ∈ zpowers z → h ∈ D ⊔ zpowers z) ∧
      (∀ h ∈ centralizer ({z} : Set K), h * h ∈ D ⊔ zpowers z) := by
  obtain ⟨Ab, hAb, hzAb, hidx, hsq⟩ := hH
  obtain ⟨eAb⟩ := hAb
  set C : Subgroup K := centralizer ({z} : Set K) with hCdef
  let z' : ↥C := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩
  let q : ↥C →* ↥C ⧸ fusionOddCore ↥C := QuotientGroup.mk' (fusionOddCore ↥C)
  have hqinj : Function.Injective q :=
    (MonoidHom.ker_eq_bot_iff q).1 ((QuotientGroup.ker_mk' _).trans hfc)
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  let qe : ↥C ≃* ↥C ⧸ fusionOddCore ↥C := MulEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  have hz'c : ∀ g : ↥C, g * z' = z' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hqc : ∀ g : ↥C ⧸ fusionOddCore ↥C, g * q z' = q z' * g := by
    intro g
    obtain ⟨g', rfl⟩ := hqsurj g
    rw [← map_mul, ← map_mul, hz'c g']
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (by simpa [z'] using hz2)
  have hqz2 : (q z') ^ 2 = 1 := by rw [← map_pow, hz'2, map_one]
  have hzAb' : q z' ∉ Ab := hzAb
  have hidx' : (Ab ⊔ Subgroup.zpowers (q z')).index = 2 := hidx
  have hsq' : ∀ h : ↥C ⧸ fusionOddCore ↥C, h * h ∈ Subgroup.zpowers (q z') →
      h ∈ Ab ⊔ Subgroup.zpowers (q z') := hsq
  have hAnorm : Ab.Normal := normal_of_alt6_index_two Ab hqc eAb hidx'
  have hD₀n : (Ab.comap q).Normal := Subgroup.Normal.comap hAnorm q
  have hkey : ∀ x : ↥C, q x ∈ Ab ⊔ Subgroup.zpowers (q z') →
      x ∈ Ab.comap q ⊔ Subgroup.zpowers z' := by
    intro x hx
    haveI := normal_zpowers_of_comm hqc
    obtain ⟨a, ha, w, hw, hax⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨a', rfl⟩ := hqsurj a
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hxeq : a' * z' ^ m = x := by
      apply hqinj
      rw [map_mul, map_zpow]
      exact hax
    rw [← hxeq]
    exact Subgroup.mul_mem_sup (show a' ∈ Ab.comap q from ha)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z') m)
  have hmapmem : ∀ x : ↥C, x ∈ Ab.comap q ⊔ Subgroup.zpowers z' →
      (x : K) ∈ (Ab.comap q).map C.subtype ⊔ Subgroup.zpowers z := by
    intro x hx
    have h1 := Subgroup.mem_map_of_mem C.subtype hx
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
    exact h1
  refine ⟨(Ab.comap q).map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro c hc d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    refine Subgroup.mem_map.2 ⟨(⟨c, hc⟩ : ↥C) * d₀ * (⟨c, hc⟩ : ↥C)⁻¹,
      hD₀n.conj_mem d₀ hd₀ ⟨c, hc⟩, ?_⟩
    simp
  ·
    have e1 : ↥((Ab.comap q).map C.subtype) ≃* ↥(Ab.comap q) :=
      (Subgroup.equivMapOfInjective (Ab.comap q) C.subtype C.subtype_injective).symm
    have hmap : (Ab.comap q).map (qe : ↥C →* ↥C ⧸ fusionOddCore ↥C) = Ab :=
      Subgroup.map_comap_eq_self_of_surjective hqsurj Ab
    have e2 : ↥(Ab.comap q) ≃* ↥Ab :=
      (MulEquiv.subgroupMap qe (Ab.comap q)).trans (MulEquiv.subgroupCongr hmap)
    exact ⟨e1.trans (e2.trans eAb)⟩
  ·
    intro hzD
    obtain ⟨d₀, hd₀, hd⟩ := Subgroup.mem_map.1 hzD
    have hd0 : d₀ = z' := Subtype.ext hd
    rw [hd0] at hd₀
    exact hzAb' (Subgroup.mem_comap.1 hd₀)
  ·
    have hCcard : Nat.card ↥C = Nat.card (↥C ⧸ fusionOddCore ↥C) :=
      Nat.card_congr qe.toEquiv
    have hPcard : Nat.card ↥(Ab ⊔ Subgroup.zpowers (q z')) = 2 * Nat.card Ab :=
      card_sup_zpowers_of_comm Ab hqc hqz2 hzAb'
    have hAcard : Nat.card Ab = 360 := by
      rw [Nat.card_congr eAb.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    have hGb := Subgroup.card_mul_index (Ab ⊔ Subgroup.zpowers (q z'))
    rw [hidx'] at hGb
    rw [hCcard, ← hGb, hPcard, hAcard]
  ·
    intro h hh hhz
    obtain ⟨h', rfl⟩ : ∃ h' : ↥C, (h' : K) = h := ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hhz
    have hsqk : h' * h' = z' ^ k := Subtype.ext (by
      show (h' : K) * h' = z ^ k
      exact hk.symm)
    have hqq : q h' * q h' ∈ Subgroup.zpowers (q z') := by
      rw [← map_mul, hsqk, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    exact hmapmem h' (hkey h' (hsq' (q h') hqq))
  ·
    intro h hh
    obtain ⟨h', rfl⟩ : ∃ h' : ↥C, (h' : K) = h := ⟨⟨h, hh⟩, rfl⟩
    have hmem : q (h' * h') ∈ Ab ⊔ Subgroup.zpowers (q z') := by
      rw [map_mul]
      exact Subgroup.mul_self_mem_of_index_two hidx' (q h')
    exact hmapmem (h' * h') (hkey (h' * h') hmem)

end CFSG.ComponentClassification.CatFC
