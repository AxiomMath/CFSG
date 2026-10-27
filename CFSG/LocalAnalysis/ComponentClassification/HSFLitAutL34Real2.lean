module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model2

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

theorem pow_two_eq_64 {k m : ℕ} (h : 2 ^ k * m = 20160) (hm : ¬ 2 ∣ m) : 2 ^ k = 64 := by
  have hk : k < 15 := by
    by_contra hk
    have : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    nlinarith
  interval_cases k <;> omega

theorem pow_two_le_64 {k : ℕ} (h : 2 ^ k ∣ 20160) : 2 ^ k ≤ 64 := by
  obtain ⟨m, hm⟩ := h
  have hk : k < 15 := by
    by_contra hk
    have : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    nlinarith
  interval_cases k <;> omega

theorem not_two_dvd_relIndex {G : Type*} [Group G] [Finite G] {P J : Subgroup G}
    (hP : IsSylowTwoIn P J) :
    ¬ 2 ∣ P.relIndex J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hP
  change ¬ 2 ∣ (P.subgroupOf J).index
  rw [← hT]
  exact T.not_dvd_index

theorem card_center_std
    {X : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R) (hX : IsPGroup 2 X)
    (hXS : Nat.card ↥(X ⊓ S) = 64) :
    Nat.card {t // t ∈ X ⊓ S ∧ ∀ s ∈ X ⊓ S, t * s = s * t} = 4 := by
  obtain ⟨c, -, -, hiff, hsurj⟩ := exists_std hXR hX hXS
  have hT : ∀ t ∈ X ⊓ S, c * t * c⁻¹ ∈ T0 := fun t ht =>
    (hiff t (mem_inf.1 ht).1).1 (mem_inf.1 ht).2
  rw [← card_center_T0]
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun t => ⟨c * t.1 * c⁻¹, hT _ t.2.1, fun u hu => ?_⟩)
      fun t t' h => Subtype.ext (by simpa using congrArg Subtype.val h)
    obtain ⟨s, hs, rfl⟩ := hsurj u hu
    rw [show c * t.1 * c⁻¹ * (c * s * c⁻¹) = c * (t.1 * s) * c⁻¹ by group, t.2.2 s hs]
    group
  · refine Nat.card_le_card_of_injective (fun u => ⟨c⁻¹ * u.1 * c, ?_, fun s hs => ?_⟩)
      fun u u' h => Subtype.ext (by simpa using congrArg Subtype.val h)
    · obtain ⟨t, ht, e⟩ := hsurj u.1 u.2.1
      rw [← e, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
      exact ht
    · have h1 := u.2.2 _ (hT s hs)
      have h2 : c⁻¹ * (u.1 * (c * s * c⁻¹)) * c = c⁻¹ * ((c * s * c⁻¹) * u.1) * c := by rw [h1]
      rw [show c⁻¹ * (u.1 * (c * s * c⁻¹)) * c = c⁻¹ * u.1 * c * s by group,
        show c⁻¹ * ((c * s * c⁻¹) * u.1) * c = s * (c⁻¹ * u.1 * c) by group] at h2
      exact h2

variable {G : Type} [Group G]

theorem mem_coreActionKernel_iff {K : Subgroup G} {p : G} (hp : p ∈ K) :
    p ∈ coreActionKernel K ↔ p ∈ zStarIn K := by
  rw [mem_zStarIn_iff hp, mem_center_iff, mem_coreActionKernel]
  constructor
  · rintro ⟨-, h⟩ e
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) e
    have hm : (j : G)⁻¹ * p⁻¹ * j * p ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem j.2) (K.inv_mem hp)) j.2) hp
    have h1 := (mem_oddIn_iff hm).1 (h j j.2)
    have e1 : (⟨(j : G)⁻¹ * p⁻¹ * j * p, hm⟩ : K) = j⁻¹ * (⟨p, hp⟩ : K)⁻¹ * j * ⟨p, hp⟩ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have : jq K j * jq K ⟨p, hp⟩ = jq K ⟨p, hp⟩ * jq K j := by
      calc jq K j * jq K ⟨p, hp⟩ = jq K ⟨p, hp⟩ * jq K j *
          ((jq K j)⁻¹ * (jq K ⟨p, hp⟩)⁻¹ * jq K j * jq K ⟨p, hp⟩) := by group
        _ = jq K ⟨p, hp⟩ * jq K j := by rw [h1, mul_one]
    exact this
  · intro h
    refine ⟨le_normalizer hp, fun j hj => ?_⟩
    have hm : j⁻¹ * p⁻¹ * j * p ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hj) (K.inv_mem hp)) hj) hp
    show _ ∈ oddIn K
    rw [mem_oddIn_iff hm]
    have e1 : (⟨j⁻¹ * p⁻¹ * j * p, hm⟩ : K) = (⟨j, hj⟩ : K)⁻¹ * (⟨p, hp⟩ : K)⁻¹ * ⟨j, hj⟩ *
        ⟨p, hp⟩ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc := h (jq K ⟨j, hj⟩)
    calc (jq K ⟨j, hj⟩)⁻¹ * (jq K ⟨p, hp⟩)⁻¹ * jq K ⟨j, hj⟩ * jq K ⟨p, hp⟩ =
        (jq K ⟨j, hj⟩)⁻¹ * (jq K ⟨p, hp⟩)⁻¹ * (jq K ⟨j, hj⟩ * jq K ⟨p, hp⟩) := by group
      _ = 1 := by rw [hc]; group

namespace Real

variable {K : Subgroup G} (ρ : Real K)

theorem img_inf_K_le (Sg : Subgroup G) : ρ.img (Sg ⊓ K) ≤ ρ.img Sg ⊓ S := by
  refine le_inf (ρ.img_mono inf_le_left) fun x hx => ?_
  obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
  exact ρ.map_K g (mem_inf.1 hg).2

theorem img_le_normalizer {H M : Subgroup G} (h : H ≤ normalizer (M : Set G)) :
    ρ.img H ≤ normalizer (ρ.img M : Set (Equiv.Perm (Fin 42))) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨m, hm, rfl⟩ := ρ.mem_img.1 hy
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ρ.phi_mem_img ((mem_normalizer_iff.1 (h hg) m).1 hm)
  · intro hy
    obtain ⟨m, hm, e⟩ := ρ.mem_img.1 hy
    have : y = ρ.φ (g⁻¹ * m * g) := by
      rw [map_mul, map_mul, e, map_inv]
      group
    rw [this]
    have hg' : (g⁻¹ : G) ∈ normalizer (M : Set G) := (normalizer (M : Set G)).inv_mem (h hg)
    have := (mem_normalizer_iff.1 hg' m).1 hm
    rw [inv_inv] at this
    exact ρ.phi_mem_img this

variable [Finite G]

theorem img_inf_K_eq {Sg : Subgroup G}
    (hS : IsSylowTwoIn Sg (normalizer (K : Set G))) :
    ρ.img (Sg ⊓ K) = ρ.img Sg ⊓ S ∧ Nat.card ↥(ρ.img Sg ⊓ S) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowTwoIn (Sg ⊓ K) K := GrS4.isSylowTwoIn_inf hS
  set κ : ↥K →* ↥S := (ρ.φ.comp (inclusion (le_normalizer : K ≤ _))).codRestrict S
    fun k => ρ.map_K k.1 k.2
  have hκ : Function.Surjective κ := by
    intro s
    obtain ⟨k, hk, e⟩ := ρ.onto_S s s.2
    exact ⟨⟨k, hk⟩, Subtype.ext e⟩
  set P' := (Sg ⊓ K).subgroupOf K
  have hmap : ρ.img (Sg ⊓ K) = (P'.map κ).map S.subtype := by
    ext x
    rw [ρ.mem_img, mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨κ ⟨g, (mem_inf.1 hg).2⟩, mem_map.2 ⟨⟨g, (mem_inf.1 hg).2⟩, mem_subgroupOf.2 hg,
        rfl⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨k, hk, rfl⟩ := mem_map.1 hs
      exact ⟨⟨k, le_normalizer k.2⟩, mem_subgroupOf.1 hk, rfl⟩
  have hcard : Nat.card ↥(ρ.img (Sg ⊓ K)) = 64 := by
    rw [hmap, card_map_of_injective S.subtype_injective]
    have hodd : ¬ 2 ∣ (P'.map κ).index := fun h2 =>
      not_two_dvd_relIndex hP (h2.trans (index_map_dvd P' hκ))
    have h1 := card_mul_index (P'.map κ)
    rw [card_S] at h1
    have hp : IsPGroup 2 ↥(P'.map κ) :=
      ((GrS4.isPGroup_of_isSylowTwoIn hP).comap_subtype (K := K)).map κ
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at h1 ⊢
    exact pow_two_eq_64 h1 hodd
  have hle : Nat.card ↥(ρ.img Sg ⊓ S) ≤ 64 := by
    have hp : IsPGroup 2 ↥(ρ.img Sg ⊓ S) :=
      (ρ.img_isPGroup (GrS4.isPGroup_of_isSylowTwoIn hS)).to_le inf_le_left
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    apply pow_two_le_64
    rw [← hk, ← card_S]
    exact card_dvd_of_le inf_le_right
  have heq := eq_of_le_of_card_ge (ρ.img_inf_K_le Sg) (by rw [hcard]; exact hle)
  exact ⟨heq, by rw [← heq, hcard]⟩

include ρ in
theorem card_le_two
    {Sg D : Subgroup G} (hS : IsSylowTwoIn Sg (normalizer (K : Set G))) (hDS : D ≤ Sg)
    (hSD : Sg ≤ normalizer (D : Set G)) (hDC : D ⊓ coreActionKernel K = ⊥)
    (hD : ∀ d ∈ D, ∀ e ∈ D, d * d = 1 → e * e = 1 → d = 1 ∨ e = 1 ∨ d = e) :
    Nat.card D ≤ 2 := by
  have hSN := hS.1
  have hS2 := GrS4.isPGroup_of_isSylowTwoIn hS
  have hsq : ∀ d ∈ D, ∀ g : ↥(normalizer (K : Set G)), (g : G) = d →
      ρ.φ g * ρ.φ g = 1 → d * d = 1 := by
    intro d hd g hg h
    rw [← map_mul, ρ.ker_iff] at h
    have : d * d ∈ D ⊓ coreActionKernel K := mem_inf.2 ⟨D.mul_mem hd hd, by rw [← hg]; exact h⟩
    rw [hDC] at this
    exact this
  have h := card_le_two_of_normal (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) (ρ.img_inf_K_eq hS).2
    (ρ.img_mono hDS) (ρ.img_le_normalizer hSD) fun x hx y hy hx2 hy2 => by
      obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
      obtain ⟨g', hg', rfl⟩ := ρ.mem_img.1 hy
      rcases hD _ hg _ hg' (hsq _ hg g rfl hx2) (hsq _ hg' g' rfl hy2) with h | h | h
      · exact Or.inl (by rw [show g = 1 from Subtype.ext h, map_one])
      · exact Or.inr (Or.inl (by rw [show g' = 1 from Subtype.ext h, map_one]))
      · exact Or.inr (Or.inr (by rw [show g = g' from Subtype.ext h]))
  rw [ρ.card_eq (hDS.trans hSN), hDC, card_bot, mul_one]
  exact h

include ρ in
theorem center_le
    {Sg E : Subgroup G} (hS : IsSylowTwoIn Sg (normalizer (K : Set G)))
    (hCE : Sg ⊓ coreActionKernel K ≤ E) (hES : E ≤ Sg) (hSE : Sg ≤ normalizer (E : Set G))
    (hEe : ∀ e ∈ E, ∀ f ∈ E, e⁻¹ * f⁻¹ * e * f ∈ coreActionKernel K ∧
      e * e ∈ coreActionKernel K)
    (h8 : 8 * Nat.card ↥(Sg ⊓ coreActionKernel K) ≤ Nat.card E) :
    Sg ⊓ K ⊓ centralizer ((Sg ⊓ K : Subgroup G) : Set G) ≤ E := by
  have hSN := hS.1
  have hS2 := GrS4.isPGroup_of_isSylowTwoIn hS
  obtain ⟨heq, h64⟩ := ρ.img_inf_K_eq hS
  have hEC : E ⊓ coreActionKernel K = Sg ⊓ coreActionKernel K :=
    le_antisymm (inf_le_inf_right _ hES) (le_inf hCE inf_le_right)
  have hE8 : 8 ≤ Nat.card (ρ.img E) := by
    have h1 := ρ.card_eq (hES.trans hSN)
    rw [hEC] at h1
    have hpos : 0 < Nat.card ↥(Sg ⊓ coreActionKernel K) := Nat.card_pos
    nlinarith
  intro z hz
  obtain ⟨⟨hzS, hzK⟩, hzc⟩ := mem_inf.1 hz
  set z' : ↥(normalizer (K : Set G)) := ⟨z, hSN hzS⟩
  have hz' : ρ.φ z' ∈ ρ.img Sg ⊓ S := heq ▸ ρ.phi_mem_img (mem_inf.2 ⟨hzS, hzK⟩)
  have hzc' : ∀ s ∈ ρ.img Sg ⊓ S, ρ.φ z' * s = s * ρ.φ z' := by
    intro s hs
    rw [← heq] at hs
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hs
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.φ (Subtype.ext (mem_centralizer_iff.1 hzc g hg).symm)
  have hmem := mem_of_center (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) h64 (ρ.img_mono hES)
    (ρ.img_le_normalizer hSE) (fun e he => by
      obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 he
      rw [← map_mul, (ρ.ker_iff _)]
      exact (hEe _ hg _ hg).2) hE8 hz' hzc'
  obtain ⟨e, he, hez⟩ := ρ.mem_img.1 hmem
  have hk : (e : G)⁻¹ * z ∈ Sg ⊓ coreActionKernel K := by
    refine mem_inf.2 ⟨Sg.mul_mem (Sg.inv_mem (hES he)) hzS, ?_⟩
    have : ρ.φ (e⁻¹ * z') = 1 := by rw [map_mul, map_inv, hez, inv_mul_cancel]
    exact (ρ.ker_iff _).1 this
  have := E.mul_mem he (hCE hk)
  rwa [mul_inv_cancel_left] at this

end Real

end CFSG.ComponentClassification.HSFLit.AutL34
