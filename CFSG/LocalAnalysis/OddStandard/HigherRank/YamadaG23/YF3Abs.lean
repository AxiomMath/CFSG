module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {P X₀ Y N : Subgroup G}

theorem ext_sq (hC : ExtCtx P X₀ Y N) {u : G} (hu : u ∈ Y) (hu2 : u ^ 2 ∈ P)
    (hcov : ∀ y ∈ Y, y ∈ X₀ ∨ ∃ m ∈ N, ∃ a ∈ X₀, y = m * u * m⁻¹ * a) :
    ∀ y ∈ Y, y ^ 2 ∈ P := by
  have hA : ∀ a ∈ X₀, a ^ 2 ∈ P := by
    intro a ha
    rcases hC.cosets a ha a⁻¹ (X₀.inv_mem ha) with h | h | h
    · rw [pow_two]; exact P.mul_mem h h
    · rw [pow_two]; simpa using P.mul_mem (P.inv_mem h) (P.inv_mem h)
    · have hsq : a * a = (a⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      rw [pow_two, hsq]
      exact P.inv_mem h
  have hB : ∀ y ∈ Y, ∀ a ∈ X₀, (y * a) ^ 2 ∈ P ↔ y ^ 2 ∈ P := by
    intro y hy a ha
    have ha2 : a ^ 2 ∈ P := hA a ha
    have hp : y⁻¹ * a * y * a⁻¹ ∈ P := by
      by_cases haP : a ∈ P
      · have h1 : y⁻¹ * a * (y⁻¹)⁻¹ ∈ P := hC.P_Y y⁻¹ (Y.inv_mem hy) a haP
        have h3 : y⁻¹ * a * (y⁻¹)⁻¹ * a⁻¹ ∈ P := P.mul_mem h1 (P.inv_mem haP)
        simpa [inv_inv] using h3
      · have hya : y⁻¹ * a * y ∈ X₀ := by
          have := hC.X₀_Y y⁻¹ (Y.inv_mem hy) a ha
          simpa [inv_inv] using this
        have hyaP : y⁻¹ * a * y ∉ P := by
          intro hmem
          apply haP
          have heq : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
          rw [heq]
          exact hC.P_Y y hy (y⁻¹ * a * y) hmem
        rcases hC.cosets a ha (y⁻¹ * a * y) hya with h | h | h
        · exact absurd h haP
        · exact absurd h hyaP
        · have heq : y⁻¹ * a * y * a⁻¹ = a * (a⁻¹ * (y⁻¹ * a * y)) * a⁻¹ := by group
          rw [heq]
          exact hC.P_Y a (hC.X₀_le ha) (a⁻¹ * (y⁻¹ * a * y)) h
    have hkey : (y * a) ^ 2 = y ^ 2 * ((y⁻¹ * a * y * a⁻¹) * a ^ 2) := by
      rw [pow_two]; group
    constructor
    · intro h
      have hy2 : y ^ 2 = (y * a) ^ 2 * ((y⁻¹ * a * y * a⁻¹) * a ^ 2)⁻¹ := by
        rw [hkey]; group
      rw [hy2]
      exact P.mul_mem h (P.inv_mem (P.mul_mem hp ha2))
    · intro h
      rw [hkey]
      exact P.mul_mem h (P.mul_mem hp ha2)
  have hN : ∀ m ∈ N, (m * u * m⁻¹) ^ 2 ∈ P := by
    intro m hm
    have hu2' : u * u ∈ P := by simpa [pow_two] using hu2
    have : (m * u * m⁻¹) ^ 2 = m * (u * u) * m⁻¹ := by rw [pow_two]; group
    rw [this]
    exact hC.P_N m hm (u * u) hu2'
  intro y hy
  rcases hcov y hy with hyX0 | ⟨m, hm, a, ha, rfl⟩
  · exact hA y hyX0
  · exact (hB (m * u * m⁻¹) (hC.Y_N m hm u hu) a ha).mpr (hN m hm)

theorem ext_comm_mem (hC : ExtCtx P X₀ Y N) (hsq : ∀ y ∈ Y, y ^ 2 ∈ P) :
    ∀ y ∈ Y, ∀ y' ∈ Y, ⁅y, y'⁆ ∈ P := by
  have hPY : P ≤ Y := hC.P_le.trans hC.X₀_le
  haveI hnorm : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hPY).mpr fun h k hh hk => hC.P_Y k hk h hh
  have hexp : ∀ g : (↥Y ⧸ P.subgroupOf Y), g ^ 2 = 1 := by
    intro g
    refine QuotientGroup.induction_on g fun y => ?_
    change (QuotientGroup.mk' (P.subgroupOf Y) y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥Y) : ↥Y ⧸ P.subgroupOf Y) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq (y : G) y.2
  have hcomm : IsMulCommutative (↥Y ⧸ P.subgroupOf Y) := by
    apply IsMulCommutative.of_comm
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexp (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexp g
        have hh := hexp h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  have hcommle : _root_.commutator ↥Y ≤ P.subgroupOf Y :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥Y)
      (N := P.subgroupOf Y)).mp hcomm
  intro y hy y' hy'
  have hmem : ⁅(⟨y, hy⟩ : ↥Y), (⟨y', hy'⟩ : ↥Y)⁆ ∈ _root_.commutator ↥Y :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcoe : ((⁅(⟨y, hy⟩ : ↥Y), (⟨y', hy'⟩ : ↥Y)⁆ : ↥Y) : G) = ⁅y, y'⁆ :=
    map_commutatorElement (f := Y.subtype) _ _
  have hmem' := hcommle hmem
  rw [Subgroup.mem_subgroupOf] at hmem'
  simpa [hcoe] using hmem'

theorem ext_normal (hC : ExtCtx P X₀ Y N) :
    (∀ y ∈ Y, ∀ c ∈ ⁅Y, N⁆ ⊔ P, y * c * y⁻¹ ∈ ⁅Y, N⁆ ⊔ P) ∧
      (∀ n ∈ N, ∀ c ∈ ⁅Y, N⁆ ⊔ P, n * c * n⁻¹ ∈ ⁅Y, N⁆ ⊔ P) := by
  have hPY : Y ≤ normalizer P := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨hC.P_Y y hy p, fun hp => ?_⟩
    have h := hC.P_Y y⁻¹ (Y.inv_mem hy) (y * p * y⁻¹) hp
    have heq : y⁻¹ * (y * p * y⁻¹) * (y⁻¹)⁻¹ = p := by group
    rwa [heq] at h
  have hPN : N ≤ normalizer P := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨hC.P_N n hn p, fun hp => ?_⟩
    have h := hC.P_N n⁻¹ (N.inv_mem hn) (n * p * n⁻¹) hp
    have heq : n⁻¹ * (n * p * n⁻¹) * (n⁻¹)⁻¹ = p := by group
    rwa [heq] at h
  have hY : Y ≤ normalizer (⁅Y, N⁆ ⊔ P : Subgroup G) :=
    (le_inf (normalizer_commutator_ge_left Y N) hPY).trans
      (inf_normalizer_le_normalizer_sup _ _)
  have hN : N ≤ normalizer (⁅Y, N⁆ ⊔ P : Subgroup G) :=
    (le_inf (normalizer_commutator_ge_right Y N) hPN).trans
      (inf_normalizer_le_normalizer_sup _ _)
  exact ⟨fun y hy c hc => ((Subgroup.mem_normalizer_iff.mp (hY hy)) c).mp hc,
    fun n hn c hc => ((Subgroup.mem_normalizer_iff.mp (hN hn)) c).mp hc⟩

theorem fpf_surj [Finite G] {V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {k : G}
    (hk : ∀ v ∈ V, k * v * k⁻¹ ∈ V) (hfix : ∀ v ∈ V, k * v * k⁻¹ = v → v = 1) :
    ∀ v ∈ V, ∃ u ∈ V, v = u * (k * u * k⁻¹)⁻¹ := by
  let f : ↥V → ↥V := fun u =>
    ⟨(u : G) * (k * (u : G) * k⁻¹)⁻¹, V.mul_mem u.2 (V.inv_mem (hk (u : G) u.2))⟩
  have hinj : Function.Injective f := by
    intro u u' h
    have h' : (u : G) * (k * (u : G) * k⁻¹)⁻¹ =
        (u' : G) * (k * (u' : G) * k⁻¹)⁻¹ := by
      simpa only [f] using congrArg Subtype.val h
    have hx : (u' : G)⁻¹ * (u : G) = k * ((u' : G)⁻¹ * (u : G)) * k⁻¹ := by
      have h1 : (u' : G)⁻¹ * ((u : G) * (k * (u : G) * k⁻¹)⁻¹) =
          (k * (u' : G) * k⁻¹)⁻¹ := by
        rw [h']; group
      calc (u' : G)⁻¹ * (u : G)
          = ((u' : G)⁻¹ * ((u : G) * (k * (u : G) * k⁻¹)⁻¹)) *
              (k * (u : G) * k⁻¹) := by group
        _ = (k * (u' : G) * k⁻¹)⁻¹ * (k * (u : G) * k⁻¹) := by rw [h1]
        _ = k * ((u' : G)⁻¹ * (u : G)) * k⁻¹ := by group
    have hxV : (u' : G)⁻¹ * (u : G) ∈ V := V.mul_mem (V.inv_mem u'.2) u.2
    have hfin : (u' : G)⁻¹ * (u : G) = 1 := hfix _ hxV hx.symm
    exact Subtype.ext ((inv_mul_eq_one.mp hfin).symm)
  intro v hv
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
  refine ⟨u, u.2, ?_⟩
  have hval : ((f u : ↥V) : G) = v := congrArg Subtype.val hu
  simpa only [f] using hval.symm

end CFSG.OddStandard.HigherRank.YamadaG23
