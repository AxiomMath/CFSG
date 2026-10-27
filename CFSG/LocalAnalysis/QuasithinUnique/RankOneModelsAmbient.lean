module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsBasic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_sylow_subgroupOf {L P : Subgroup G} (hPL : P ≤ L) (hp : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ (P.subgroupOf L).index) :
    ∃ Q : Sylow 2 L, (Q : Subgroup L) = P.subgroupOf L :=
  ⟨(hp.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm).toSylow hidx, rfl⟩

theorem map_closure_involutions_subgroupOf {L P : Subgroup G} (hPL : P ≤ L) :
    (Subgroup.closure {x : L | x ∈ P.subgroupOf L ∧ x ^ 2 = 1}).map L.subtype =
      Subgroup.closure {x : G | x ∈ P ∧ x ^ 2 = 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hy2⟩, rfl⟩
    exact ⟨hy, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hy2, OneMemClass.coe_one]⟩
  · rintro ⟨hxP, hx2⟩
    exact ⟨⟨x, hPL hxP⟩, ⟨hxP, Subtype.ext (by rw [Subgroup.coe_pow]; exact hx2)⟩, rfl⟩

theorem coe_mem_normalizer_map_subtype_iff {L : Subgroup G} {V' : Subgroup L} {n : L} :
    (n : G) ∈ Subgroup.normalizer ((V'.map L.subtype : Subgroup G) : Set G) ↔
      n ∈ Subgroup.normalizer (V' : Set L) := by
  have hmem : ∀ y : L, (y : G) ∈ V'.map L.subtype ↔ y ∈ V' := fun y =>
    Subgroup.mem_map_iff_mem L.subtype_injective
  constructor
  · intro hn
    refine Subgroup.mem_normalizer_iff.2 fun y => ?_
    rw [← hmem, ← hmem, show ((n * y * n⁻¹ : L) : G) = (n : G) * y * (n : G)⁻¹ from rfl]
    exact Subgroup.mem_normalizer_iff.1 hn y
  · intro hn
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hh
      exact ⟨n * y * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, rfl⟩
    · obtain ⟨y, hy, hyh⟩ := hh
      have hhL : h ∈ L := by
        have : h = (n : G)⁻¹ * y * n := by
          rw [show (y : G) = (n : G) * h * (n : G)⁻¹ from hyh]
          group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem n.2) y.2) n.2
      refine ⟨⟨h, hhL⟩, (Subgroup.mem_normalizer_iff.1 hn ⟨h, hhL⟩).2 ?_, rfl⟩
      have : (n * ⟨h, hhL⟩ * n⁻¹ : L) = y := Subtype.ext hyh.symm
      rw [this]
      exact hy

theorem isElemAbelian_map_subtype {L : Subgroup G} {V' : Subgroup L} (h : IsElemAbelian 2 V') :
    IsElemAbelian 2 (V'.map L.subtype) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, ha, rfl⟩ := x
    obtain ⟨_, b, hb, rfl⟩ := y
    have hab : a * b = b * a := congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    apply Subtype.ext
    change L.subtype a * L.subtype b = L.subtype b * L.subtype a
    rw [← map_mul, ← map_mul, hab]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.2 a ha, map_one]

namespace HasFieldScalarStructure

variable {L : Subgroup G} {V' : Subgroup L} {q : ℕ}

theorem ambient (h : HasFieldScalarStructure V' q) :
    (∀ a ∈ V'.map L.subtype, a ≠ 1 → ∀ b ∈ V'.map L.subtype, b ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer ((V'.map L.subtype : Subgroup G) : Set G), n⁻¹ * a * n = b) ∧
    (∀ n ∈ L ⊓ Subgroup.normalizer ((V'.map L.subtype : Subgroup G) : Set G),
      ∀ a ∈ V'.map L.subtype, a ≠ 1 → n⁻¹ * a * n = a → ∀ x ∈ V'.map L.subtype, n⁻¹ * x * n = x) ∧
    (∃ g ∈ L ⊓ Subgroup.normalizer ((V'.map L.subtype : Subgroup G) : Set G),
      ∀ n ∈ L ⊓ Subgroup.normalizer ((V'.map L.subtype : Subgroup G) : Set G), ∃ k : ℕ,
        ∀ x ∈ V'.map L.subtype, n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ ha1 _ ⟨b, hb, rfl⟩ hb1
    obtain ⟨n, hn, hnab⟩ := h.exists_normalizer_conj_inv ha hb
      (fun h1 => ha1 (by rw [Subgroup.coe_subtype, h1, OneMemClass.coe_one]))
      (fun h1 => hb1 (by rw [Subgroup.coe_subtype, h1, OneMemClass.coe_one]))
    exact ⟨(n : G), ⟨n.2, coe_mem_normalizer_map_subtype_iff.2 hn⟩, congrArg Subtype.val hnab⟩
  · rintro n ⟨hnL, hn⟩ _ ⟨a, ha, rfl⟩ ha1 hna _ ⟨x, hx, rfl⟩
    have hn' : (⟨n, hnL⟩ : L) ∈ Subgroup.normalizer (V' : Set L) :=
      coe_mem_normalizer_map_subtype_iff.1 hn
    have := h.centralizes_of_fixed hn' ha
      (fun h1 => ha1 (by rw [Subgroup.coe_subtype, h1, OneMemClass.coe_one]))
      (Subtype.ext hna) x hx
    exact congrArg Subtype.val this
  · obtain ⟨g, hg, hgen⟩ := h.exists_generator
    refine ⟨(g : G), ⟨g.2, coe_mem_normalizer_map_subtype_iff.2 hg⟩, ?_⟩
    rintro n ⟨hnL, hn⟩
    obtain ⟨k, hk⟩ := hgen ⟨n, hnL⟩ (coe_mem_normalizer_map_subtype_iff.1 hn)
    refine ⟨k, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hk x hx)

end HasFieldScalarStructure

end CFSG.QuasithinUnique
