module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem inf_le_center_of_isQuasisimple_of_odd {U K : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) (hKq : IsQuasisimple ↥K) (hK2 : ∃ k ∈ K, orderOf k = 2) :
    K ⊓ U ≤ (center ↥K).map K.subtype := by
  have hN : ((K ⊓ U).subgroupOf K).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.normal_subgroupOf
  have hNne : (K ⊓ U).subgroupOf K ≠ ⊤ := by
    intro htop
    obtain ⟨k, hkK, hk2⟩ := hK2
    have hkU : k ∈ U := by
      have hmem : (⟨k, hkK⟩ : ↥K) ∈ (K ⊓ U).subgroupOf K := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hmem).2
    have hdvd : orderOf k ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hkU
    rw [hk2] at hdvd
    exact hU.not_two_dvd_nat hdvd
  have hNle : (K ⊓ U).subgroupOf K ≤ center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN with h | h
    · exact absurd h hNne
    · exact h
  calc K ⊓ U = ((K ⊓ U).subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
    _ ≤ (center ↥K).map K.subtype := Subgroup.map_mono hNle

omit [Finite X] in
theorem commute_of_commutator_mem_of_odd {U K : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) (hKq : IsQuasisimple ↥K) (hK2 : ∃ k ∈ K, orderOf k = 2) {u : X}
    (hu : u ∈ K) (hcomm : ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ U) : ∀ k ∈ K, u * k = k * u := by
  have : Group.IsPerfect ↥K := hKq.1
  have hKU : K ⊓ U ≤ (center ↥K).map K.subtype :=
    inf_le_center_of_isQuasisimple_of_odd hU hKq hK2
  let x : ↥K := ⟨u, hu⟩
  have hxc : ∀ e : ↥K, ⁅x, e⁆ ∈ center ↥K := by
    intro e
    have hmemK : u * (e : X) * u⁻¹ * (e : X)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hu e.2) (K.inv_mem hu)) (K.inv_mem e.2)
    have hmemU : u * (e : X) * u⁻¹ * (e : X)⁻¹ ∈ U := hcomm e e.2
    obtain ⟨z, hz, hzval⟩ :=
      Subgroup.mem_map.mp (hKU (Subgroup.mem_inf.mpr ⟨hmemK, hmemU⟩))
    have heq : (⟨u * (e : X) * u⁻¹ * (e : X)⁻¹, hmemK⟩ : ↥K) = z :=
      Subtype.ext hzval.symm
    have hmem : (⟨u * (e : X) * u⁻¹ * (e : X)⁻¹, hmemK⟩ : ↥K) ∈ center ↥K :=
      heq.symm ▸ hz
    have hval : (⟨u * (e : X) * u⁻¹ * (e : X)⁻¹, hmemK⟩ : ↥K) = x * e * x⁻¹ * e⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hval] at hmem
    simpa [commutatorElement_def] using hmem
  have hcentral : (⟨u, hu⟩ : ↥K) ∈ center ↥K := by
    let ψ : ↥K →* ↥(center ↥K) :=
      { toFun := fun e => ⟨⁅x, e⁆, hxc e⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun e f => by
          apply Subtype.ext
          have hf := Subgroup.mem_center_iff.mp (hxc f) e
          simp only [commutatorElement_def, Subgroup.coe_mul] at hf ⊢
          calc x * (e * f) * x⁻¹ * (e * f)⁻¹ =
              x * e * x⁻¹ * e⁻¹ * (e * (x * f * x⁻¹ * f⁻¹) * e⁻¹) := by group
            _ = x * e * x⁻¹ * e⁻¹ * (x * f * x⁻¹ * f⁻¹) := by rw [hf]; group }
    have hker : commutator ↥K ≤ ψ.ker := by
      rw [commutator_eq_closure, closure_le]
      rintro _ ⟨a, b, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.mp (ψ a).2 (ψ b : ↥K)).symm
    rw [Subgroup.mem_center_iff]
    intro e
    have he : e ∈ ψ.ker := hker (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top e)
    have h1 : ⁅x, e⁆ = 1 := congrArg Subtype.val he
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  intro k hk
  have h1 : (⟨k, hk⟩ : ↥K) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨k, hk⟩ :=
    Subgroup.mem_center_iff.mp hcentral ⟨k, hk⟩
  exact (congrArg Subtype.val h1).symm

theorem le_map_of_perfect_le_centralizer_quotient {U : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) {t : X} (ht : t ^ 2 = 1) {K : Subgroup X}
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) → ⁅L, L⁆ = L → L ≤ K)
    {L : Subgroup (X ⧸ U)} (hLt : L ≤ centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)))
    (hL : ⁅L, L⁆ = L) : L ≤ K.map (QuotientGroup.mk' U) := by
  classical
  have hCmap : (centralizer ({t} : Set X)).map (QuotientGroup.mk' U) =
      centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)) := by
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq
      (H := X) (p := 2) Nat.prime_two (W := ⊤) (N := U) le_top
      (Nat.coprime_two_left.mpr hU) ht
    rw [top_inf_eq, Subgroup.map_top_of_surjective (QuotientGroup.mk' U)
      (QuotientGroup.mk'_surjective U), top_inf_eq] at h
    exact h
  have hLle : L ≤ (centralizer ({t} : Set X)).map (QuotientGroup.mk' U) := hCmap.symm ▸ hLt
  have hL0map : (L.comap (QuotientGroup.mk' U) ⊓ centralizer ({t} : Set X)).map
      (QuotientGroup.mk' U) = L := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_left
    · intro x hx
      have hxC : x ∈ (centralizer ({t} : Set X)).map (QuotientGroup.mk' U) := hLle hx
      obtain ⟨c, hcC, hcπ⟩ := Subgroup.mem_map.mp hxC
      exact Subgroup.mem_map.mpr
        ⟨c, ⟨Subgroup.mem_comap.mpr (by rw [hcπ]; exact hx), hcC⟩, hcπ⟩
  have hex : ∃ n : ℕ, ∃ P : Subgroup X,
      P ≤ L.comap (QuotientGroup.mk' U) ⊓ centralizer ({t} : Set X) ∧
        P.map (QuotientGroup.mk' U) = L ∧ Nat.card P = n :=
    ⟨_, _, le_rfl, hL0map, rfl⟩
  obtain ⟨P, hPle, hPmap, hPcard⟩ := Nat.find_spec hex
  have hmin : ∀ P' : Subgroup X,
      P' ≤ L.comap (QuotientGroup.mk' U) ⊓ centralizer ({t} : Set X) →
        P'.map (QuotientGroup.mk' U) = L → P' ≤ P → P' = P := by
    intro P' hP'le hP'map hle'
    have hcard : Nat.card P ≤ Nat.card P' := by
      rw [hPcard]
      exact Nat.find_min' hex ⟨P', hP'le, hP'map, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle' hcard
  have hcommle : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have hPperf : ⁅P, P⁆ = P := by
    refine hmin ⁅P, P⁆ (hcommle.trans hPle) ?_ hcommle
    rw [Subgroup.map_commutator, hPmap, hL]
  calc L = P.map (QuotientGroup.mk' U) := hPmap.symm
    _ ≤ K.map (QuotientGroup.mk' U) :=
        Subgroup.map_mono (hperf P (hPle.trans inf_le_right) hPperf)

theorem isComponent_map_centralizer_quotient {U : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) {t : X} (ht : t ^ 2 = 1) {K : Subgroup X}
    (hKt : K ≤ centralizer ({t} : Set X)) (hKq : IsQuasisimple ↥K)
    (hKn : (K.subgroupOf (centralizer ({t} : Set X))).Normal)
    (hK2 : ∃ k ∈ K, orderOf k = 2) :
    K.map (QuotientGroup.mk' U) ≤ centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)) ∧
      IsComponent ((K.map (QuotientGroup.mk' U)).subgroupOf
        (centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)))) := by
  classical
  let C : Subgroup X := centralizer ({t} : Set X)
  let π : X →* X ⧸ U := QuotientGroup.mk' U
  let Cq : Subgroup (X ⧸ U) := centralizer ({π t} : Set (X ⧸ U))
  have hCmap : C.map π = Cq := by
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq
      (H := X) (p := 2) Nat.prime_two (W := ⊤) (N := U) le_top
      (Nat.coprime_two_left.mpr hU) ht
    rw [top_inf_eq, Subgroup.map_top_of_surjective (QuotientGroup.mk' U)
      (QuotientGroup.mk'_surjective U), top_inf_eq] at h
    simpa [C, Cq, π] using h
  have hKC : K.map π ≤ Cq := by
    rintro _ ⟨k, hkK, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hkt : t * k = k * t := Subgroup.mem_centralizer_iff.mp (hKt hkK) t rfl
    rw [← map_mul, ← map_mul, hkt]
  have hnotU : ¬ K ≤ U := by
    rintro hKU
    obtain ⟨k, hkK, hk2⟩ := hK2
    have hdvd : orderOf k ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U (hKU hkK)
    rw [hk2] at hdvd
    exact hU.not_two_dvd_nat hdvd
  have hKmap : CFSG.IsQuasisimple ↥(K.map π) :=
    CFSG.LocalCores.isQuasisimple_map hKq π
      (by simpa [π, QuotientGroup.ker_mk'] using hnotU)
  have hKn' : ((K.map π).subgroupOf Cq).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnK : (n : X ⧸ U) ∈ K.map π := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨k, hkK, hkval⟩ := Subgroup.mem_map.mp hnK
    have hgC : (g : X ⧸ U) ∈ C.map π := hCmap.symm ▸ g.2
    obtain ⟨c, hcC, hcval⟩ := Subgroup.mem_map.mp hgC
    have hkc : c * k * c⁻¹ ∈ K := by
      have h1 : (⟨k, hKt hkK⟩ : ↥C) ∈ K.subgroupOf C := Subgroup.mem_subgroupOf.mpr hkK
      have h2 := hKn.conj_mem (⟨k, hKt hkK⟩ : ↥C) h1 (⟨c, hcC⟩ : ↥C)
      simpa using Subgroup.mem_subgroupOf.mp h2
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨c * k * c⁻¹, hkc, ?_⟩
    have hcoe : ((g * n * g⁻¹ : ↥Cq) : X ⧸ U) =
        (g : X ⧸ U) * (n : X ⧸ U) * (g : X ⧸ U)⁻¹ := by simp
    rw [hcoe, map_mul, map_mul, map_inv, hcval, hkval]
  refine ⟨hKC, ?_⟩
  have hKq' : CFSG.IsQuasisimple ↥((K.map π).subgroupOf Cq) :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKC)).mpr hKmap
  exact ⟨hKq', hKn'.isSubnormal⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
