module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Kernel
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

variable {R E H : Subgroup G} {T : Subgroup (Equiv.Perm ↥(pointsIn R E))}

theorem exists_translationSubgroup (hD : PointsData R E H) (hT : TranslationData R E T) :
    ∃ P₀ : Subgroup G, P₀ ≤ normalizer (E : Set G) ∧
      normalizer (E : Set G) ≤ normalizer (P₀ : Set G) ∧
      centralizer (E : Set G) ≤ P₀ ∧
      (∀ p ∈ P₀, ∀ q ∈ P₀, p * p ∈ centralizer (E : Set G) ∧
        p * q * p⁻¹ * q⁻¹ ∈ centralizer (E : Set G)) ∧
      (P₀ ⊓ centralizer (E : Set G)).relIndex P₀ = 16 ∧
      (∀ Q ∈ pointsIn R E, ∃ p ∈ P₀, rightConjugate R p = Q) ∧
      (∀ p ∈ P₀, rightConjugate R p = R → p ∈ centralizer (E : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCn := centralizerIn_normal E
  set N := normalizer (E : Set G) with hNdef
  set ρ := pointsAction R E with hρ
  set C := centralizerIn E with hC
  have hCk : ∀ c ∈ C, ρ c = 1 := fun c hc => pointsAction_eq_one_of_mem_centralizer hc
  set Ñ : Subgroup ↥N := T.comap ρ with hÑ
  have hÑn : ∀ m : ↥N, m ∈ normalizer (Ñ : Set ↥N) := fun m => by
    rw [mem_normalizer_iff]
    intro x
    have hmT : ρ m ∈ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))) :=
      hT.range_le ⟨m, rfl⟩
    show ρ x ∈ T ↔ ρ (m * x * m⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.mp hmT (ρ x)
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 Ñ
  obtain ⟨hSÑ, hS2, hSidx⟩ := isSylowOf_iff.mp hS
  have hST : T ≤ S.map ρ := by
    have h1 : (S ⊔ ρ.ker).relIndex Ñ ∣ S.relIndex Ñ := relIndex_dvd_of_le_left Ñ le_sup_left
    have h2 : (S ⊔ ρ.ker).relIndex Ñ = (S.map ρ).relIndex T := by
      rw [← comap_map_eq, hÑ, relIndex_comap, map_comap_eq, inf_eq_right.mpr hT.le_range]
    have h3 : (S.map ρ).relIndex T ∣ 2 ^ 4 := by
      have : (S.map ρ).relIndex T ∣ Nat.card T := by
        show ((S.map ρ).subgroupOf T).index ∣ _
        exact Subgroup.index_dvd_card _
      rwa [hT.card] at this
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have hi0 : i = 0 := by
      by_contra hi0
      apply hSidx
      rw [h2, hieq] at h1
      exact (dvd_pow_self 2 hi0).trans h1
    rw [hi0, pow_zero] at hieq
    exact relIndex_eq_one.mp hieq
  set P₀' := S ⊔ C with hP₀'
  have hmemP : ∀ p ∈ P₀', ∃ s ∈ S, ∃ c ∈ C, p = s * c := by
    intro p hp
    have hp' : p ∈ ((S ⊔ C : Subgroup ↥N) : Set ↥N) := hp
    rw [mul_normal S C, Set.mem_mul] at hp'
    obtain ⟨s, hs, c, hc, rfl⟩ := hp'
    exact ⟨s, hs, c, hc, rfl⟩
  have hP₀Ñ : P₀' ≤ Ñ := sup_le hSÑ fun c hc => by
    show ρ c ∈ T
    rw [hCk c hc]
    exact T.one_mem
  have hP₀ker : ∀ p ∈ P₀', ρ p = 1 → p ∈ C := by
    intro p hp hp1
    obtain ⟨s, hs, c, hc, rfl⟩ := hmemP p hp
    have hs1 : ρ s = 1 := by
      rw [map_mul, hCk c hc, mul_one] at hp1
      exact hp1
    obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
    have hn' : (s : G) ^ 2 ^ n = 1 := by
      have := congrArg (fun z : ↥S => ((z : ↥N) : G)) hn
      simpa using this
    have hsC : s ∈ C := hD.mem_centralizer_of_pow_eq_one s.2
      (mem_normalizer_of_pointsAction_eq_one hs1) hn'
    exact C.mul_mem hsC hc
  have hP₀n : ∀ m : ↥N, ∀ p ∈ P₀', m * p * m⁻¹ ∈ P₀' := by
    intro m p hp
    obtain ⟨s, hs, c, hc, rfl⟩ := hmemP p hp
    have hS' : IsSylowOf 2 (rightConjugate S m⁻¹) Ñ := by
      have h := AschbacherTheorem3.isSylowOf_rightConjugate hS m⁻¹
      rwa [(rightConjugate_eq_self_iff Ñ m⁻¹).mpr (hÑn m⁻¹)] at h
    obtain ⟨w, hwÑ, hw⟩ := IsSylowOf.exists_mem_conj hS hS'
    have hms : m * s * m⁻¹ ∈ rightConjugate S m⁻¹ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hs
    have hs' := (hw _).mp hms
    obtain ⟨s₀, hs₀, hs₀w⟩ := hST hwÑ
    set s' := w⁻¹ * (m * s * m⁻¹) * w with hs'def
    set k := s₀⁻¹ * w with hkdef
    have hk1 : ρ k = 1 := by rw [hkdef, map_mul, map_inv, hs₀w, inv_mul_cancel]
    have hs'Ñ : ρ s'⁻¹ ∈ T := by
      rw [map_inv]
      exact T.inv_mem (hSÑ hs')
    have hD' := commutator_mem_of_mem_translations hD hT hs'Ñ hk1
    have heq : m * s * m⁻¹ =
        (s₀ * s' * s₀⁻¹) * (s₀ * (s'⁻¹ * k * s'⁻¹⁻¹ * k⁻¹) * s₀⁻¹) := by
      rw [hs'def, hkdef]
      group
    have hmc : m * c * m⁻¹ ∈ C := hCn.conj_mem c hc m
    have e2 : m * (s * c) * m⁻¹ = (m * s * m⁻¹) * (m * c * m⁻¹) := by group
    rw [e2, heq]
    refine P₀'.mul_mem (P₀'.mul_mem (mem_sup_left ?_) (mem_sup_right ?_)) (mem_sup_right hmc)
    · exact S.mul_mem (S.mul_mem hs₀ hs') (S.inv_mem hs₀)
    · exact hCn.conj_mem _ hD' s₀
  have hP₀T : P₀'.map ρ = T := by
    refine le_antisymm ?_ (hST.trans (map_mono le_sup_left))
    rintro _ ⟨p, hp, rfl⟩
    exact hP₀Ñ hp
  have hidx : (C.subgroupOf P₀').index = 16 := by
    set f := ρ.comp P₀'.subtype with hf
    have hker : f.ker = C.subgroupOf P₀' := by
      ext p
      rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, coe_subtype]
      exact ⟨hP₀ker p p.2, hCk p⟩
    have hrange : f.range = P₀'.map ρ := by
      rw [hf, MonoidHom.range_comp, range_subtype]
    rw [← hker, index_ker, hrange, hP₀T, hT.card]
  set P₀ := P₀'.map N.subtype with hP₀
  have hP₀N : P₀ ≤ N := map_subtype_le _
  have hCN : centralizer (E : Set G) ≤ N := centralizer_le_normalizer _
  have hCP : centralizer (E : Set G) ≤ P₀ := fun c hc =>
    ⟨⟨c, hCN hc⟩, mem_sup_right (show (⟨c, hCN hc⟩ : ↥N) ∈ C from hc), rfl⟩
  set p₀ : ↥(pointsIn R E) := ⟨R, hD.self_mem⟩ with hp₀
  refine ⟨P₀, hP₀N, fun n hn => ?_, hCP, ?_, ?_, ?_, ?_⟩
  ·
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨n, hn⟩ * p * ⟨n, hn⟩⁻¹, hP₀n _ p hp, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      refine ⟨⟨n, hn⟩⁻¹ * p * ⟨n, hn⟩⁻¹⁻¹, hP₀n _ p hp, ?_⟩
      have hpx' : (p : G) = n * x * n⁻¹ := hpx
      simp only [coe_subtype, coe_mul, coe_inv, inv_inv, hpx']
      group
  ·
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have hpT : ρ p ∈ T := hP₀Ñ hp
    have hqT : ρ q ∈ T := hP₀Ñ hq
    constructor
    · have h1 : ρ (p * p) = 1 := by
        rw [map_mul, ← sq]
        exact hT.elem.2 _ hpT
      exact hP₀ker _ (P₀'.mul_mem hp hp) h1
    · have hcomm : ρ p * ρ q = ρ q * ρ p :=
        congrArg Subtype.val (hT.elem.1.is_comm.comm ⟨_, hpT⟩ ⟨_, hqT⟩)
      have h1 : ρ (p * q * p⁻¹ * q⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
        group
      exact hP₀ker _ (P₀'.mul_mem (P₀'.mul_mem (P₀'.mul_mem hp hq) (P₀'.inv_mem hp))
        (P₀'.inv_mem hq)) h1
  ·
    have hinf : P₀ ⊓ centralizer (E : Set G) = (P₀' ⊓ C).map N.subtype := by
      rw [map_inf_eq _ _ _ N.subtype_injective, hC, subgroupOf_map_subtype,
        inf_eq_left.mpr hCN]
    rw [hinf, relIndex_map_map_of_injective _ _ N.subtype_injective, inf_relIndex_left]
    exact hidx
  ·
    intro Q hQ
    obtain ⟨t, ht, htp⟩ := hT.trans p₀ ⟨Q, hQ⟩
    obtain ⟨s, hs, hst⟩ := hST ht
    refine ⟨((s⁻¹ : ↥N) : G), ⟨s⁻¹, P₀'.inv_mem (mem_sup_left hs), rfl⟩, ?_⟩
    have h := congrArg (fun q : ↥(pointsIn R E) => (q : Subgroup G)) htp
    simp only at h
    rw [← hst, coe_pointsAction_apply] at h
    simpa using h
  ·
    rintro _ ⟨p, hp, rfl⟩ hpR
    have hpN : (p : G)⁻¹ ∈ normalizer (R : Set G) :=
      inv_mem ((rightConjugate_eq_self_iff R _).mp hpR)
    have hfix : ρ p p₀ = p₀ := by
      apply Subtype.ext
      rw [coe_pointsAction_apply]
      exact (rightConjugate_eq_self_iff R _).mpr hpN
    have h1 : ρ p = 1 := hT.eq_one_of_apply_eq (hP₀Ñ hp) hfix
    exact hP₀ker p hp h1

end CFSG.ComponentClassification.AS81
