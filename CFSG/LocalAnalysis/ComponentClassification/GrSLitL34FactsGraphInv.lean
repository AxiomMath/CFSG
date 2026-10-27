module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphCert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem comm_mul_eq_one {E : Type*} [Group E] {x₁ x₂ y c₁ c₂ : E} (hc₂ : c₂ ∈ center E)
    (h₁ : x₁ * y * x₁⁻¹ * y⁻¹ = c₁) (h₂ : x₂ * y * x₂⁻¹ * y⁻¹ = c₂)
    (h : x₁ * x₂ * y = y * (x₁ * x₂)) : c₂ * c₁ = 1 := by
  have e₁ : x₁ * y * x₁⁻¹ = c₁ * y := by rw [← h₁]; group
  have e₂ : x₂ * y * x₂⁻¹ = c₂ * y := by rw [← h₂]; group
  have hc := (mem_center_iff.mp hc₂ x₁).symm
  have key : c₂ * c₁ * y = 1 * y := by
    calc c₂ * c₁ * y = c₂ * (x₁ * y * x₁⁻¹) := by rw [e₁, mul_assoc]
      _ = c₂ * x₁ * y * x₁⁻¹ := by group
      _ = x₁ * c₂ * y * x₁⁻¹ := by rw [hc]
      _ = x₁ * (c₂ * y) * x₁⁻¹ := by group
      _ = x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ := by rw [e₂]
      _ = x₁ * x₂ * y * (x₁ * x₂)⁻¹ := by group
      _ = 1 * y := by rw [h]; group
  exact mul_right_cancel key

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem IsQSetting.xc_of_comm
    (h : IsQSetting q l) {κ : ℕ} {ζ : E} (hκ : KClass l κ ζ) (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (hζc : ζ ∈ center E) {k m : ℕ} (hk : k < 16) (hm : m < 16) {e : E}
    (he : q e = wordPerm (tg k) * wordPerm (tg (4 * m)))
    (hc : ∀ w, w = 4 ∨ w = 8 → e * l (cv (tw w)) = l (cv (tw w)) * e) : xc κ k m = true := by
  have hbit : ∀ w, w = 4 ∨ w = 8 → cbit κ k w = cbit κ (4 * m) w := by
    intro w hw
    have hw64 : w < 64 := by rcases hw with rfl | rfl <;> norm_num
    obtain ⟨hb₁, -⟩ := commBit_cbit hκ.mem hk hw
    obtain ⟨-, hb₂⟩ := commBit_cbit hκ.mem hm hw
    have c₁ := h.lift_comm_of_bit hκ hζ hb₁
    have c₂ := h.lift_comm_of_bit hκ hζ hb₂
    set x₁ := l (cv (tw k))
    set x₂ := l (cv (tw (4 * m)))
    set y := l (cv (tw w))
    have hu : (x₁ * x₂)⁻¹ * e ∈ center E := by
      rw [← h.ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, h.q_lift (by omega),
        h.q_lift (by omega), he, inv_mul_cancel]
    have hcomm : x₁ * x₂ * y = y * (x₁ * x₂) := by
      have h1 := hc w hw
      have hu' := mem_center_iff.mp hu y
      calc x₁ * x₂ * y = x₁ * x₂ * y * ((x₁ * x₂)⁻¹ * e) * ((x₁ * x₂)⁻¹ * e)⁻¹ := by group
        _ = x₁ * x₂ * ((x₁ * x₂)⁻¹ * e) * y * ((x₁ * x₂)⁻¹ * e)⁻¹ := by
          rw [mul_assoc (x₁ * x₂) y, hu', ← mul_assoc]
        _ = e * y * ((x₁ * x₂)⁻¹ * e)⁻¹ := by group
        _ = y * e * ((x₁ * x₂)⁻¹ * e)⁻¹ := by rw [h1]
        _ = y * (x₁ * x₂) := by group
    have hc₂ : (if cbit κ (4 * m) w then ζ else 1) ∈ center E := by
      split_ifs
      · exact hζc
      · exact one_mem _
    have h1 := comm_mul_eq_one hc₂ c₁ c₂ hcomm
    cases h₁ : cbit κ k w <;> cases h₂ : cbit κ (4 * m) w <;> simp only [h₁, h₂] at h1 ⊢
    · simp at h1
      exact absurd h1 hζ1
    · simp at h1
      exact absurd h1 hζ1
  simp only [xc, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hbit 4 (Or.inl rfl), hbit 8 (Or.inr rfl)⟩

variable {G : Type} [Group G]

theorem jq_mem_of_mem_sup {J P B : Subgroup G} (hBJ : B ≤ J) (hPJ : P ≤ J)
    {M : Subgroup (Jhat J)} (hB : ∀ b (hb : b ∈ B), jq J ⟨b, hBJ hb⟩ ∈ M)
    (hZ : center (Jhat J) ≤ M) {y : G} (hy : y ∈ B ⊔ (P ⊓ zStarIn J)) (hyJ : y ∈ J) :
    jq J ⟨y, hyJ⟩ ∈ M := by
  have hle : B ⊔ (P ⊓ zStarIn J) ≤ (M.comap (jq J)).map J.subtype := by
    refine sup_le (fun b hb => ⟨⟨b, hBJ hb⟩, hB b hb, rfl⟩) fun z hz => ?_
    have hzJ : z ∈ J := hPJ hz.1
    exact ⟨⟨z, hzJ⟩, hZ ((mem_zStarIn_iff hzJ).1 hz.2), rfl⟩
  obtain ⟨j, hj, hjy⟩ := hle hy
  have : j = ⟨y, hyJ⟩ := Subtype.ext hjy
  rw [← this]
  exact hj

theorem exists_involution_realization {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) {x : G} (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1)
    (hxK : x ∉ withKernel J) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ t ∈ S, ∃ e, q e = t) (hqker : q.ker = center (Jhat J)) :
    ∃ r ∈ R, r * r = 1 ∧ r ∉ S ∧ ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹ := by
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hxN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj t ht
      have h1 := hr (betaHat J hxN e)
      rw [betaHat_betaHat J hxN hx2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  refine ⟨r, hrR, hr2, fun hrS => ?_, hr⟩
  obtain ⟨e₀, he₀⟩ := hqsurj r hrS
  exact hxK (mem_withKernel_of_realization hJ hxN hqker (e₀ := e₀) fun e => by
    rw [hr e, he₀])

theorem graphInvertModZ :
    ∀ (G : Type) [Group G] [Finite G] (J P B : Subgroup G) (c : G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
      IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 → B ≤ P →
      (∀ y ∈ P, (∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ B ⊔ (P ⊓ zStarIn J)) →
      c ∈ normalizer (J : Set G) → c ∈ normalizer (P : Set G) → c * c = 1 →
      c ∉ withKernel J → (∀ b ∈ B, c * b = b * c) →
      ∀ s ∈ P, (∀ b ∈ B, s * b = b * s) → c * s * c * s ∈ zStarIn J := by
  intro G _ _ J P B c hJ hL hP hcyc h4 hBP hB hcN hcP hc2 hcK hcB s hs hsB
  have hPJ : P ≤ J := hP.1
  have hBJ : B ≤ J := hBP.trans hPJ
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  obtain ⟨ζe, -⟩ := exists_zeta hP hqker
  have hkcyc : IsCyclic q.ker := isCyclic_of_surjective ζe.toMonoidHom ζe.surjective
  have hk4 : Nat.card q.ker = 4 := by rw [← Nat.card_congr ζe.toEquiv, h4]
  obtain ⟨g, hg1, hg⟩ := cyclic_four hk4
  have hζk : ((g * g : q.ker) : Jhat J) ∈ q.ker := (g * g).2
  have hζ1 : ((g * g : q.ker) : Jhat J) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hζ2 : ((g * g : q.ker) : Jhat J) * ((g * g : q.ker) : Jhat J) = 1 :=
    congrArg Subtype.val (((hg (g * g)).1).2 (Or.inr rfl))
  obtain ⟨κ, hκ⟩ := hQ.exists_kclass hkcyc hk4 hζk hζ1 hζ2
  have hζc : ((g * g : q.ker) : Jhat J) ∈ center (Jhat J) := hqker ▸ hζk
  obtain ⟨r, hrR, hr2, hrS, hr⟩ := exists_involution_realization hJ hcN hc2 hcK hqS hqsurj hqker
  have hZ0 : ∀ t ∈ Z0, ∃ y ∈ P, ∃ hyJ : y ∈ J, y ∈ B ⊔ (P ⊓ zStarIn J) ∧
      q (jq J ⟨y, hyJ⟩) = t := by
    intro t ht
    obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht.2)
    obtain ⟨y, hyP, hyJ, rfl⟩ := (hT e).1 (he ▸ ht.2)
    exact ⟨y, hyP, hyJ, (hB y hyP).1 ((mem_Z0_iff_comm hP hqsurj hqker hT hyP).1 (he ▸ ht)), he⟩
  have hw : ∀ w, w = 4 ∨ w = 8 → wordPerm (tg w) ∈ Z0 := fun w hw =>
    mem_Z0.2 ⟨w, by rcases hw with rfl | rfl <;> simp, rfl⟩
  have hrw : ∀ w, w = 4 ∨ w = 8 → r * wordPerm (tg w) = wordPerm (tg w) * r := by
    intro w hw'
    obtain ⟨y, -, hyJ, hyBZ, hyq⟩ := hZ0 _ (hw w hw')
    have hM := jq_mem_of_mem_sup hBJ hPJ (M := (centralizer {r}).comap q) (fun b hb => ?_)
      (fun e he => ?_) hyBZ hyJ
    · rw [mem_comap, mem_centralizer_singleton_iff, hyq] at hM
      exact hM.symm
    · rw [mem_comap, mem_centralizer_singleton_iff]
      have h1 := hr (jq J ⟨b, hBJ hb⟩)
      have h2 : conjJ J hcN ⟨b, hBJ hb⟩ = ⟨b, hBJ hb⟩ := Subtype.ext (by
        show c⁻¹ * b * c = b
        rw [mul_assoc, ← hcB b hb, ← mul_assoc, inv_mul_cancel, one_mul])
      rw [betaHat_jq, h2] at h1
      calc q (jq J ⟨b, hBJ hb⟩) * r = r * q (jq J ⟨b, hBJ hb⟩) * r⁻¹ * r := by rw [← h1]
        _ = r * q (jq J ⟨b, hBJ hb⟩) := by group
    · rw [← hqker] at he
      rw [mem_comap, MonoidHom.mem_ker.mp he]
      exact one_mem _
  have hlc : ∀ s' (hs'P : s' ∈ P), (∀ b ∈ B, s' * b = b * s') → ∀ w, w = 4 ∨ w = 8 →
      jq J ⟨s', hPJ hs'P⟩ * l (cv (tw w)) = l (cv (tw w)) * jq J ⟨s', hPJ hs'P⟩ := by
    intro s' hs'P hs'B w hw'
    obtain ⟨y, -, hyJ, hyBZ, hyq⟩ := hZ0 _ (hw w hw')
    have hM := jq_mem_of_mem_sup hBJ hPJ (M := centralizer {jq J ⟨s', hPJ hs'P⟩})
      (fun b hb => ?_) (center_le_centralizer _) hyBZ hyJ
    · rw [mem_centralizer_singleton_iff] at hM
      have hw64 : w < 64 := by rcases hw' with rfl | rfl <;> norm_num
      set e := jq J ⟨s', hPJ hs'P⟩
      set Y := jq J ⟨y, hyJ⟩
      have hu : Y⁻¹ * l (cv (tw w)) ∈ center (Jhat J) := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hyq, hQ.q_lift hw64, inv_mul_cancel]
      have hu' := mem_center_iff.mp hu e
      calc e * l (cv (tw w)) = e * Y * (Y⁻¹ * l (cv (tw w))) := by group
        _ = Y * e * (Y⁻¹ * l (cv (tw w))) := by rw [hM]
        _ = Y * (Y⁻¹ * l (cv (tw w)) * e) := by rw [mul_assoc, hu']
        _ = l (cv (tw w)) * e := by group
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hs'B b hb).symm
  have hbits : ∀ s' (hs'P : s' ∈ P), (∀ b ∈ B, s' * b = b * s') →
      ∃ k < 16, ∃ m < 16, xc κ k m = true ∧
        wordPerm (tg k) * wordPerm (tg (4 * m)) = q (jq J ⟨s', hPJ hs'P⟩) := by
    intro s' hs'P hs'B
    obtain ⟨k, hk, m, hm, hkm⟩ := exists_decomp ((hT _).2 ⟨s', hs'P, hPJ hs'P, rfl⟩)
    exact ⟨k, hk, m, hm, hQ.xc_of_comm hκ hζ2 hζ1 hζc hk hm hkm.symm (hlc s' hs'P hs'B), hkm⟩
  have hsc : c⁻¹ * s * c ∈ P := conj_mem_of_mem_normalizer hcP hs
  have hscB : ∀ b ∈ B, c⁻¹ * s * c * b = b * (c⁻¹ * s * c) := by
    intro b hb
    have h1 : c⁻¹ * b = b * c⁻¹ := by
      calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcB b hb]
        _ = b * c⁻¹ := by group
    calc c⁻¹ * s * c * b = c⁻¹ * s * (c * b) := by group
      _ = c⁻¹ * s * (b * c) := by rw [hcB b hb]
      _ = c⁻¹ * (s * b) * c := by group
      _ = c⁻¹ * (b * s) * c := by rw [hsB b hb]
      _ = c⁻¹ * b * s * c := by group
      _ = b * c⁻¹ * s * c := by rw [h1]
      _ = b * (c⁻¹ * s * c) := by group
  obtain ⟨k, hk, m, hm, hx, hkm⟩ := hbits s hs hsB
  obtain ⟨k', hk', m', hm', hx', hkm'⟩ := hbits _ hsc hscB
  have he : r * (wordPerm (tg k) * wordPerm (tg (4 * m))) * r⁻¹ =
      wordPerm (tg k') * wordPerm (tg (4 * m')) := by
    rw [hkm, hkm', ← hr, betaHat_jq]
    rfl
  have hinv := invert_spec hrR hr2 hrS (hrw 4 (Or.inl rfl)) (hrw 8 (Or.inr rfl)) hκ.mem hk hm
    hk' hm' hx hx' he
  rw [hkm, hkm'] at hinv
  have hmem : c⁻¹ * s * c * s ∈ J := J.mul_mem (hPJ hsc) (hPJ hs)
  have hz : c⁻¹ * s * c * s ∈ zStarIn J := by
    rw [mem_zStarIn_iff hmem, ← hqker, MonoidHom.mem_ker]
    have e1 : (⟨c⁻¹ * s * c * s, hmem⟩ : J) = ⟨c⁻¹ * s * c, hPJ hsc⟩ * ⟨s, hPJ hs⟩ := rfl
    rw [e1, map_mul, map_mul]
    exact hinv
  rwa [inv_eq_of_mul_eq_one_right hc2] at hz

theorem graphInvertModZ_inf
    [Finite G]
    {J S B : Subgroup G} {c : G} (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hP : IsSylowTwoIn (S ⊓ J) J) (hSN : S ≤ normalizer (J : Set G))
    (hcyc : IsCyclic ↥(S ⊓ zStarIn J)) (h4 : Nat.card ↥(S ⊓ zStarIn J) = 4) (hBP : B ≤ S ⊓ J)
    (hB : ∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
      y ∈ B ⊔ (S ⊓ zStarIn J))
    (hcS : c ∈ S) (hc2 : c * c = 1) (hcK : c ∉ withKernel J) (hcB : ∀ b ∈ B, c * b = b * c) :
    ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c * s ∈ zStarIn J := by
  intro s hs
  have hZJ : zStarIn J ≤ J := Subgroup.map_subtype_le _
  have hZ : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by rw [inf_assoc, inf_of_le_right hZJ]
  rw [← hZ] at hcyc h4 hB
  have hcN : c ∈ normalizer (J : Set G) := hSN hcS
  have hcP : c ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_inf]
    rw [← mem_normalizer_iff.mp hcN h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨S.mul_mem (S.mul_mem hcS h1) (S.inv_mem hcS), h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := S.mul_mem (S.mul_mem (S.inv_mem hcS) h1) hcS
      rwa [show c⁻¹ * (c * h * c⁻¹) * c = h by group] at this
  exact graphInvertModZ G J (S ⊓ J) B c hJ hL hP hcyc h4 hBP hB hcN hcP hc2 hcK hcB s hs.1
    fun b hb => ((mem_centralizer_iff.mp hs.2) b hb).symm

end CFSG.ComponentClassification.GrSLit.L34Facts
