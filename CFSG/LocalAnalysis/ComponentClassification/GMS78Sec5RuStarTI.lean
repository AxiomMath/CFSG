module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Push

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open scoped MatrixGroups

@[expose] def jordanGL32 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

theorem jordanGL32_sq_ne_one : jordanGL32 ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun A : GL (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) h
  revert this
  decide

theorem orderOf_jordanGL32 : orderOf jordanGL32 = 4 := by
  have h4 : jordanGL32 ^ 4 = 1 := by
    apply Units.ext
    decide
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using jordanGL32_sq_ne_one)
    (by simpa using h4)

theorem card_le_four_of_sq_eq_one_GL32 {Q : Subgroup (GL (Fin 3) (ZMod 2))}
    (hQ : ∀ q ∈ Q, q ^ 2 = 1) : Nat.card Q ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := fun q => ⟨1, Subtype.ext (by simpa using hQ q q.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hdvd : 2 ^ k ∣ 168 := hk ▸ GHarris.card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card Q
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h16
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  exfalso
  have hcard : ∀ P : Sylow 2 (GL (Fin 3) (ZMod 2)), Nat.card P = 8 := fun P => by
    simpa using LiteratureLocal.Order504.card_sylow_eq_of_card_eq (p := 2) (a := 3) (m := 21)
      (by rw [GHarris.card_GL32_gh]; norm_num) (by norm_num) P
  obtain ⟨P, hP⟩ := hQp.exists_le_sylow
  have hQP : (P : Subgroup (GL (Fin 3) (ZMod 2))) = Q :=
    (eq_of_le_of_card_ge hP (by rw [hcard, hk]; norm_num)).symm
  have hJp : IsPGroup 2 (zpowers jordanGL32) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, orderOf_jordanGL32]; norm_num)
  obtain ⟨P₀, hP₀⟩ := hJp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) P₀ P
  have hmem : g * jordanGL32 * g⁻¹ ∈ Q := by
    rw [← hQP, ← hg]
    change g * jordanGL32 * g⁻¹ ∈ ((g • P₀ : Sylow 2 _) : Set (GL (Fin 3) (ZMod 2)))
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      show g⁻¹ * (g * jordanGL32 * g⁻¹) * g = jordanGL32 by group]
    exact hP₀ (mem_zpowers jordanGL32)
  apply jordanGL32_sq_ne_one
  have h2 := hQ _ hmem
  rw [sq, show g * jordanGL32 * g⁻¹ * (g * jordanGL32 * g⁻¹) = g * (jordanGL32 * jordanGL32) * g⁻¹
    by group, mul_inv_eq_one, mul_eq_left] at h2
  rw [sq, h2]

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_centralizer_of_le_normalizer {B P : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hPB : P ≤ normalizer (B : Set G)) (hP : ∀ p ∈ P, p ^ 2 = 1)
    (hP4 : 4 < Nat.card P) : ∃ a ∈ P, a ≠ 1 ∧ a ∈ centralizer (B : Set G) := by
  obtain ⟨e⟩ := GHarris.nonempty_mulAut_equiv_GL32 hB hB8
  set N := normalizer (B : Set G) with hNdef
  set φ : ↥N →* GL (Fin 3) (ZMod 2) := e.toMonoidHom.comp B.normalizerMonoidHom with hφ
  set P' : Subgroup ↥N := P.subgroupOf N with hP'def
  have hP' : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv
  have hQ := card_le_four_of_sq_eq_one_GL32 (Q := P'.map φ) (by
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, show p ^ 2 = 1 from Subtype.ext (hP p (mem_subgroupOf.mp hp)), map_one])
  by_contra hno
  push Not at hno
  have hker : (φ.domRestrict P').ker = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply] at hp
    have h2 : B.normalizerMonoidHom (p : N) = 1 := by
      apply e.injective
      rw [map_one]
      exact hp
    have hmem : ((p : N) : G) ∈ centralizer (B : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      have h3 := congrArg (fun ψ : MulAut B => ((ψ ⟨b, hb⟩ : B) : G)) h2
      simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
      calc b * ((p : N) : G) = ((p : N) : G) * b * ((p : N) : G)⁻¹ * ((p : N) : G) := by
            rw [h3]
        _ = ((p : N) : G) * b := by group
    rw [mem_bot]
    by_contra hp1
    exact hno _ (mem_subgroupOf.mp p.2) (fun h => hp1 (Subtype.ext (Subtype.ext h))) hmem
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hcard : Nat.card (P'.map φ) = Nat.card P' := by
    rw [← MonoidHom.domRestrict_range]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  omega

section TI

variable {F : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_conj_mem_star
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G)) {c g : G}
    (hc : c ∈ F) (hcg : g⁻¹ * c * g ∈ F) (hc1 : c ≠ 1) : g ∈ normalizer (F : Set G) := by
  have ha1 : g⁻¹ * c * g ≠ 1 := fun h => hc1 (by
    calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨n, hn, hna⟩ := htrans _ hcg c hc ha1 hc1
  have hng : n⁻¹ * g ∈ centralizer ({g⁻¹ * c * g} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc n⁻¹ * g * (g⁻¹ * c * g) = n⁻¹ * c * g := by group
      _ = n⁻¹ * (n * (g⁻¹ * c * g) * n⁻¹) * g := by rw [hna]
      _ = g⁻¹ * c * g * (n⁻¹ * g) := by group
  have h1 := hstar _ hcg ha1 hng
  rw [show g = n * (n⁻¹ * g) by group]
  exact mul_mem hn h1

omit [Finite G] in
theorem centralizer_le_normalizer_conj
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G)) {g b : G}
    (hb : g⁻¹ * b * g ∈ F) (hb1 : b ≠ 1) :
    centralizer ({b} : Set G) ≤
      normalizer ((F.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro z hz
  have hb1' : g⁻¹ * b * g ≠ 1 := fun h => hb1 (by
    calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hw : g⁻¹ * z * g ∈ normalizer (F : Set G) := hstar _ hb hb1' (by
    rw [mem_centralizer_singleton_iff] at hz ⊢
    calc g⁻¹ * z * g * (g⁻¹ * b * g) = g⁻¹ * (z * b) * g := by group
      _ = g⁻¹ * (b * z) * g := by rw [hz]
      _ = g⁻¹ * b * g * (g⁻¹ * z * g) := by group)
  rw [mem_normalizer_iff]
  intro y
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(g⁻¹ * z * g) * a * (g⁻¹ * z * g)⁻¹, (mem_normalizer_iff.mp hw a).mp ha, by group⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨(g⁻¹ * z * g)⁻¹ * a * (g⁻¹ * z * g), ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hw) a).mp ha
      simpa [mul_assoc] using this
    · calc g * ((g⁻¹ * z * g)⁻¹ * a * (g⁻¹ * z * g)) * g⁻¹ = z⁻¹ * (g * a * g⁻¹) * z := by group
        _ = z⁻¹ * (z * y * z⁻¹) * z := by rw [hay]
        _ = y := by group

theorem false_of_conj_mem_of_mem_centralizer (hFel : IsElemAbelian 2 F) (hF8 : Nat.card F = 8)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G))
    (hE64 : ∀ P : Subgroup G, P ≤ centralizer (F : Set G) → IsElemAbelian 2 P → Nat.card P ≤ 32)
    {x g : G} (hxR : x ∈ centralizer (F : Set G)) (hxF : x ∉ F) (hxg : g⁻¹ * x * g ∈ F) :
    False := by
  set B : Subgroup G := F.map (MulAut.conj g).toMonoidHom with hBdef
  have hmemB : ∀ y, y ∈ B ↔ g⁻¹ * y * g ∈ F := fun y => by
    simp only [hBdef, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [mul_assoc] using ha
    · intro h
      exact ⟨_, h, by group⟩
  have hx1 : x ≠ 1 := fun h => hxF (h ▸ one_mem F)
  have hxB : x ∈ B := (hmemB x).mpr hxg
  have hBel : IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := mem_map.mp b.2
      have hc := hFel.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      have hc' : a' * b' = b' * a' := congrArg Subtype.val hc
      show (a : G) * b = b * a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, hc']
    · have h1 := hFel.2 _ ((hmemB y).mp hy)
      have h2 : y ^ 2 = g * (g⁻¹ * y * g) ^ 2 * g⁻¹ := by
        rw [sq, sq]
        group
      rw [h2, h1]
      group
  have hB8 : Nat.card B = 8 := by
    rw [hBdef, card_map_of_injective (MulAut.conj g).injective, hF8]
  have hFN : F ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer_conj hstar hxg hx1
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxR a ha))
  obtain ⟨a, haF, ha1, haB⟩ := exists_mem_centralizer_of_le_normalizer hBel hB8 hFN
    (fun p hp => hFel.2 p hp) (by rw [hF8]; norm_num)
  have hBN : B ≤ normalizer (F : Set G) := fun b hb =>
    hstar a haF ha1 (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haB b hb))
  have hinf : F ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [mem_bot]
    by_contra hc1
    obtain ⟨hcF, hcB⟩ := mem_inf.mp hc
    have hgN := mem_normalizer_of_conj_mem_star htrans hstar hcF ((hmemB c).mp hcB) hc1
    exact hxF (by
      rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group]
      exact (mem_normalizer_iff.mp hgN _).mp hxg)
  have hcomm : ∀ a' ∈ F, ∀ b ∈ B, a' * b = b * a' := by
    intro a' ha' b hb
    have h1 : a' * b * a'⁻¹ * b⁻¹ ∈ F ⊓ B := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show a' * b * a'⁻¹ * b⁻¹ = a' * (b * a'⁻¹ * b⁻¹) by group]
        exact mul_mem ha' ((mem_normalizer_iff.mp (hBN hb) _).mp (inv_mem ha'))
      · exact mul_mem ((mem_normalizer_iff.mp (hFN ha') b).mp hb) (inv_mem hb)
    rw [hinf, mem_bot] at h1
    calc a' * b = a' * b * a'⁻¹ * b⁻¹ * (b * a') := by group
      _ = b * a' := by rw [h1, one_mul]
  have hsup : F ⊔ B ≤ centralizer (F : Set G) := by
    refine sup_le (fun a' ha' => mem_centralizer_iff.mpr fun a'' ha'' => ?_) fun b hb =>
      mem_centralizer_iff.mpr fun a'' ha'' => hcomm a'' ha'' b hb
    exact congrArg Subtype.val (hFel.1.is_comm.comm ⟨a'', ha''⟩ ⟨a', ha'⟩)
  have hcard : Nat.card (F ⊔ B : Subgroup G) = 64 := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hBN
    rw [hinf, card_bot, mul_one, hF8, hB8] at h1
    exact h1
  have hdecomp : ∀ z ∈ F ⊔ B, ∃ b ∈ B, ∃ a' ∈ F, b * a' = z := fun z hz =>
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hBN (by rwa [sup_comm] at hz)
  have hel : IsElemAbelian 2 (F ⊔ B : Subgroup G) := by
    refine ⟨⟨⟨fun z w => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨b, hb, a', ha', hz⟩ := hdecomp z z.2
      obtain ⟨b', hb', a'', ha'', hw⟩ := hdecomp w w.2
      show (z : G) * w = w * z
      rw [← hz, ← hw]
      have h1 := hcomm a' ha' b' hb'
      have h2 := hcomm a'' ha'' b hb
      have h3 : b * b' = b' * b := congrArg Subtype.val (hBel.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
      have h4 : a' * a'' = a'' * a' :=
        congrArg Subtype.val (hFel.1.is_comm.comm ⟨a', ha'⟩ ⟨a'', ha''⟩)
      calc b * a' * (b' * a'') = b * (a' * b') * a'' := by group
        _ = b * (b' * a') * a'' := by rw [h1]
        _ = (b * b') * (a' * a'') := by group
        _ = (b' * b) * (a'' * a') := by rw [h3, h4]
        _ = b' * (b * a'') * a' := by group
        _ = b' * (a'' * b) * a' := by rw [← h2]
        _ = b' * a'' * (b * a') := by group
    · obtain ⟨b, hb, a', ha', rfl⟩ := hdecomp z hz
      have h1 := hcomm a' ha' b hb
      calc (b * a') ^ 2 = b * (a' * b) * a' := by rw [sq]; group
        _ = b * (b * a') * a' := by rw [h1]
        _ = b ^ 2 * a' ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [hBel.2 b hb, hFel.2 a' ha', one_mul]
  have := hE64 _ hsup hel
  omega

theorem false_of_centralizer_le_normalizer_of_sylow (h34 : NoStronglyClosedAbelian G)
    (hFel : IsElemAbelian 2 F) (hF8 : Nat.card F = 8)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G))
    (hE64 : ∀ P : Subgroup G, P ≤ centralizer (F : Set G) → IsElemAbelian 2 P → Nat.card P ≤ 32)
    (S : Sylow 2 G) (hFS : F ≤ S)
    (hD : ∀ y ∈ (S : Subgroup G), y ∉ centralizer (F : Set G) → ∀ g : G, g * y * g⁻¹ ∉ F) :
    False := by
  refine h34 S F hFS hFel.1 ?_ fun a ha g hg => ?_
  · intro hb
    rw [hb, card_bot] at hF8
    norm_num at hF8
  · by_cases hR : g⁻¹ * a * g ∈ centralizer (F : Set G)
    · by_contra hF
      refine false_of_conj_mem_of_mem_centralizer hFel hF8 htrans hstar hE64 hR hF (g := g⁻¹) ?_
      simpa [mul_assoc] using ha
    · exact absurd (by simpa [mul_assoc] using ha) (hD _ hg hR g)

end TI

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {y d : G}

theorem exists_conj_eq_of_mem_gmsA
    (hS : SzR G L T R 1 y d) (hR₂ : IsR₂ L T R R₂ d) {a b : G} (ha : a ∈ gmsA L T)
    (hb : b ∈ gmsA L T) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ normalizer (gmsA L T : Set G), n * a * n⁻¹ = b := by
  obtain ⟨k, hk⟩ := hS.exists_pow_conj_eq_gmsA ha hb ha1 hb1
  refine ⟨(d ^ k)⁻¹, inv_mem (pow_mem (hS.normalizer_le_normalizer_gmsA hR₂ hS.mem_normalizer) k),
    ?_⟩
  rw [inv_inv]
  exact hk

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
