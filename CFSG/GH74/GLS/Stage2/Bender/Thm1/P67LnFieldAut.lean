module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Glue
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Lift

variable {K : Type} [Field K] {n : ℕ}

theorem conj_mem_range_of_fix {k : Subfield K} {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {y : projectiveSL n K} (hy : fieldAut n K σ y = y) {c : projectiveSL n K}
    (hc : c ∈ (linearSubfieldInclusion n k).range) :
    y * c * y⁻¹ ∈ (linearSubfieldInclusion n k).range := by
  obtain ⟨g, hgk, rfl⟩ := mem_range_linearSubfieldInclusion.mp hc
  obtain ⟨γ, rfl⟩ := proj_surjective n K y
  rw [fieldAut_proj] at hy
  have hz := proj_eq_proj_iff.mp hy.symm
  rw [scalars_eq_center] at hz
  obtain ⟨Zc, hZc⟩ : ∃ Zc : SpecialLinearGroup (Fin n) K, Zc = γ⁻¹ * SpecialLinearGroup.map σ.toRingHom γ :=
    ⟨_, rfl⟩
  have hZcc : Zc ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by rw [hZc]; exact hz
  have hσγ : SpecialLinearGroup.map σ.toRingHom γ = γ * Zc := by rw [hZc]; group
  have hσg : SpecialLinearGroup.map σ.toRingHom g = g := by
    apply Subtype.ext
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (hk _).mp (hgk i j)
  obtain ⟨e, he⟩ : ∃ e : SpecialLinearGroup (Fin n) K, e = γ * g * γ⁻¹ := ⟨_, rfl⟩
  have hmap : SpecialLinearGroup.map σ.toRingHom e = e := by
    rw [he, map_mul, map_mul, map_inv, hσg, hσγ, _root_.mul_inv_rev]
    have h1 : Zc * g = g * Zc := (Subgroup.mem_center_iff.mp hZcc g).symm
    calc γ * Zc * g * (Zc⁻¹ * γ⁻¹) = γ * (Zc * g * Zc⁻¹) * γ⁻¹ := by group
      _ = γ * g * γ⁻¹ := by rw [h1]; group
  refine mem_range_linearSubfieldInclusion.mpr ⟨e, fun i j => ?_, ?_⟩
  · rw [hk]
    have h2 := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) hmap
    simpa [SpecialLinearGroup.map_apply_coe] using h2
  · rw [he]; simp [map_mul, map_inv]

end Lift

section Aux

theorem commutator_eq_self_of_simple {G : Type*} [Group G] (H : Subgroup G) (hs : IsSimpleGroup ↥H)
    (hn : ¬ ∀ x y : ↥H, x * y = y * x) : ⁅H, H⁆ = H := by
  have hmap : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmc := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥H)) (H₂ := ⊤) H.subtype
  rw [hmap] at hmc
  rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥H) with h | h
  · exfalso
    apply hn
    intro x y
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ commutator ↥H :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot] at hxy
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hxy)
  · rw [← hmc]
    have : (⁅(⊤ : Subgroup ↥H), ⊤⁆ : Subgroup ↥H) = ⊤ := h
    rw [this, hmap]

theorem eq_one_of_mem_zpowers_coprime {G : Type*} [Group G] {b a : G} {r c : ℕ} (hbr : b ^ r = 1)
    (hcop : Nat.Coprime c r) (ha : a ∈ Subgroup.zpowers b) (hac : a ^ c = 1) : a = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have har : (b ^ m) ^ r = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hbr, _root_.one_zpow]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hac)
    (orderOf_dvd_of_pow_eq_one har))

end Aux

section Core

variable {K : Type} [Field K] [Finite K]

theorem false_of_fieldAut_mem {n : ℕ} (hn : 3 ≤ n) {r : ℕ} {V Z : Subgroup (MulAut (projectiveSL n K))}
    (h2 : N2Cfg (projectiveSL n K) r V Z) (h3 : N3Deriv (projectiveSL n K) V Z)
    {σ : K ≃+* K} (hσ : orderOf σ = r) (hb : fieldAut n K σ ∈ V) : False := by
  classical
  obtain ⟨hr, -, -, -, hZab, -, hZcop, hZbot, hcomm⟩ := h2
  have hcen : Subgroup.center (projectiveSL n K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn
  have hinj := mulAut_conj_injective_of_center_bot hcen
  set b : MulAut (projectiveSL n K) := fieldAut n K σ with hbdef
  have hbr : b ^ r = 1 := by rw [hbdef, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  have hbne : b ≠ 1 := by
    intro h
    have := KCLinearSubfield.orderOf_fieldAut (K := K) (n := n) hn σ
    rw [← hbdef, h, orderOf_one, hσ] at this
    exact hr.one_lt.ne this
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  set H : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range with hHdef
  obtain ⟨hHs, hHn⟩ := simple_nonabelian_range_linearSubfieldInclusion (n := n) (K := K) hn k
  have hHfix : H ≤ fixSub b := by
    rintro _ ⟨x, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) x
  have hHperf : ⁅H, H⁆ = H := commutator_eq_self_of_simple H hHs hHn
  have hHder : H ≤ ⁅fixSub b, fixSub b⁆ := hHperf ▸ Subgroup.commutator_mono hHfix hHfix
  have hnorm : ∀ c ∈ H, MulAut.conj c ∈ normalizer (Z : Set (MulAut (projectiveSL n K))) :=
    fun c hc => h3 b hb hbne c (hHder hc)
  set D : Subgroup (projectiveSL n K) := Z.comap (MulAut.conj : projectiveSL n K →* MulAut _) with hDdef
  have hDmem : ∀ u, u ∈ D ↔ MulAut.conj u ∈ Z := fun u => Iff.rfl
  have hDab : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := by
    intro u hu v hv
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ hu _ hv
  have hDfix : ∀ u ∈ D, b u = u := by
    intro u hu
    have h1 := hcomm b hb _ hu
    apply hinj
    rw [← mulAut_conj_conj, h1]
    group
  have hDnorm : ∀ c ∈ H, ∀ u ∈ D, c * u * c⁻¹ ∈ D := by
    intro c hc u hu
    have := (Subgroup.mem_normalizer_iff.mp (hnorm c hc) (MulAut.conj u)).mp hu
    rw [hDmem, map_mul, map_mul, map_inv]
    exact this
  have hconjH : ∀ y ∈ fixSub b, ∀ c ∈ H, y * c * y⁻¹ ∈ H := fun y hy c hc =>
    conj_mem_range_of_fix hk (mem_fixSub.mp hy) hc
  have hDH : ∀ x ∈ D, x ∈ H → x = 1 := by
    let A : Subgroup ↥H := (D ⊓ H).subgroupOf H
    have hAn : A.Normal := ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨?_, (g * a * g⁻¹).2⟩
      have := hDnorm g g.2 a ha.1
      simpa using this⟩
    have : A.Normal := hAn
    rcases hHs.eq_bot_or_eq_top_of_normal A with h | h
    · intro x hx hxH
      have : (⟨x, hxH⟩ : ↥H) ∈ A := Subgroup.mem_subgroupOf.mpr ⟨hx, hxH⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hHn
      intro x y
      have hx : (x : projectiveSL n K) ∈ D := by
        have : x ∈ A := h ▸ Subgroup.mem_top x
        exact (Subgroup.mem_subgroupOf.mp this).1
      have hy : (y : projectiveSL n K) ∈ D := by
        have : y ∈ A := h ▸ Subgroup.mem_top y
        exact (Subgroup.mem_subgroupOf.mp this).1
      exact Subtype.ext (hDab _ hx _ hy)
  have hDcommH : ∀ c ∈ H, ∀ u ∈ D, c * u = u * c := by
    intro c hc u hu
    have hw : c * u * c⁻¹ * u⁻¹ ∈ D := D.mul_mem (hDnorm c hc u hu) (D.inv_mem hu)
    have hwH : c * u * c⁻¹ * u⁻¹ ∈ H := by
      have h1 := hconjH u (mem_fixSub.mpr (hDfix u hu)) c⁻¹ (H.inv_mem hc)
      have : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [this]
      exact H.mul_mem hc h1
    have := hDH _ hw hwH
    calc c * u = (c * u * c⁻¹ * u⁻¹) * (u * c) := by group
      _ = u * c := by rw [this, one_mul]
  have hfixH : ∀ a : MulAut (projectiveSL n K), (∀ y ∈ H, a y = y) → a ∈ Subgroup.zpowers b := by
    intro a ha
    have := fixingSubgroup_range_linearSubfieldInclusion (n := n) (K := K) hk hn
    rw [← this]
    exact (mem_fixingSubgroup_iff _).mpr (fun y hy => ha y hy)
  have hZcard : ∀ a ∈ Z, a ^ Nat.card ↥Z = 1 := by
    intro a ha
    have h' : (⟨a, ha⟩ : ↥Z) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  have hD1 : ∀ u ∈ D, u = 1 := by
    intro u hu
    have hfix : ∀ y ∈ H, MulAut.conj u y = y := by
      intro y hy
      rw [MulAut.conj_apply]
      have := hDcommH y hy u hu
      calc u * y * u⁻¹ = (y * u) * u⁻¹ := by rw [this]
        _ = y := by group
    have hconj1 : MulAut.conj u = 1 :=
      eq_one_of_mem_zpowers_coprime hbr hZcop (hfixH _ hfix) (hZcard _ hu)
    exact hinj (by rw [hconj1, map_one])
  have hZfix : ∀ z ∈ Z, ∀ c ∈ H, z c = c := by
    intro z hz c hc
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm c hc) z).mp hz
    have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hz)
    have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
      have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
        have := mulAut_conj_conj z c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
          = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have h6 := hD1 _ h4
    have : z c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h6
      simpa using this
    have := congrArg (fun t => t⁻¹) this
    simpa using this
  apply hZbot
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_zpowers_coprime hbr hZcop (hfixH z (hZfix z hz)) (hZcard z hz)

theorem false_of_noninner {n : ℕ} (hn : 3 ≤ n) {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hrp : r ≠ p) {V Z : Subgroup (MulAut (projectiveSL n K))}
    (h2 : N2Cfg (projectiveSL n K) r V Z) (h3 : N3Deriv (projectiveSL n K) V Z)
    (hVD : ¬ V ≤ linearAutGroup n K) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  obtain ⟨b, hbV, hbD⟩ := IsConcreteLE.not_le_iff_exists.mp hVD
  obtain ⟨hr, hr2, hVe, -⟩ := id h2
  have : Fact r.Prime := ⟨hr⟩
  have hbr : b ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian b hbV
  have hb1 : b ≠ 1 := fun h => hbD (h ▸ one_mem _)
  have hord : orderOf b = r := orderOf_eq_prime hbr hb1
  have hbE : b ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_eq_one (m := r) hn hr2 hbr
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent (n := n) (K := K) hp hf hn hK
  obtain ⟨-, σ, hσ, ⟨h, hhD, hbh⟩, -⟩ := hdesc r hr hrp b hbE hbD hord
  have h2' := h2.map_mulEquiv (MulAut.congr (h⁻¹ : MulAut (projectiveSL n K)))
  have h3' := h3.map_mulEquiv (h⁻¹ : MulAut (projectiveSL n K))
  refine false_of_fieldAut_mem hn h2' h3' hσ ⟨b, hbV, ?_⟩
  show MulAut.congr (h⁻¹ : MulAut (projectiveSL n K)) b = fieldAut n K σ
  rw [congr_eq_mul_mul_inv, hbh]
  group

end Core

end CFSG.GH74.GLS.Stage2.Bender.Thm1
