module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Odd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace RankFour

theorem card_closure_le_two_pow {G : Type*} [Group G] [Finite G] (s : Finset G)
    (hcomm : ∀ a ∈ closure (s : Set G), ∀ b ∈ closure (s : Set G), a * b = b * a)
    (h2 : ∀ a ∈ closure (s : Set G), a * a = 1) :
    Nat.card (closure (s : Set G)) ≤ 2 ^ s.card := by
  let _ : CommGroup ↥(closure (s : Set G)) :=
    { (inferInstance : Group _) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hexp : Monoid.exponent ↥(closure (s : Set G)) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
      rw [Subgroup.coe_pow, sq]; exact h2 g g.2)
  have h1 := card_dvd_exponent_pow_rank ↥(closure (s : Set G))
  have h3 := Subgroup.rank_closure_finset_le_card s
  have hpos : 0 < 2 ^ Group.rank ↥(closure (s : Set G)) := by positivity
  calc Nat.card ↥(closure (s : Set G)) ≤ 2 ^ Group.rank ↥(closure (s : Set G)) :=
        Nat.le_of_dvd hpos (h1.trans (pow_dvd_pow_of_dvd hexp _))
    _ ≤ 2 ^ s.card := Nat.pow_le_pow_right two_pos h3

theorem isPGroup_of_isElemTwo {G : Type*} [Group G] {E : Subgroup G} (hE : GrSLit.IsElemTwo E) :
    IsPGroup 2 E := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact hE.2 x x.2)⟩

theorem isElemTwo_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂) {E : Subgroup G₁}
    (hE : GrSLit.IsElemTwo E) : GrSLit.IsElemTwo (E.map φ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE.2 x hx, map_one]

theorem exists_isElemTwo_map_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    {φ : G₁ →* G₂} (hφ : ¬ 2 ∣ Nat.card φ.ker) {Ê : Subgroup G₂} (hÊ : GrSLit.IsElemTwo Ê)
    (hle : Ê ≤ φ.range) :
    ∃ E : Subgroup G₁, GrSLit.IsElemTwo E ∧ E.map φ = Ê ∧ Nat.card E = Nat.card Ê := by
  obtain ⟨E, hE2, hEmap⟩ := GSThmB.Eight.exists_isPGroup_map_eq (isPGroup_of_isElemTwo hÊ) hle
  have hinj := GSThmB.Eight.injOn_of_isPGroup hφ hE2
  have hmem : ∀ x ∈ E, φ x ∈ Ê := fun x hx => hEmap ▸ mem_map_of_mem φ hx
  refine ⟨E, ⟨fun x hx y hy => ?_, fun x hx => ?_⟩, hEmap, ?_⟩
  · refine hinj (mul_mem hx hy) (mul_mem hy hx) ?_
    rw [map_mul, map_mul, hÊ.1 _ (hmem x hx) _ (hmem y hy)]
  · refine hinj (mul_mem hx hx) (one_mem E) ?_
    rw [map_mul, hÊ.2 _ (hmem x hx), map_one]
  · rw [← hEmap, GSThmB.Eight.card_map_of_isPGroup hφ hE2]

end RankFour

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem card_le_sixteen_of_isElemTwo (hKG : AutPSL2SylowInput) (h : Standing t L p f)
    {E : Subgroup X} (hEH : E ≤ centralizer ({t} : Set X)) (hE : GrSLit.IsElemTwo E) :
    Nat.card E ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := ((RankFour.isPGroup_of_isElemTwo hE).comap_subtype :
    IsPGroup 2 (E.subgroupOf (centralizer ({t} : Set X)))).exists_le_sylow
  have hS : IsSylowOf 2 ((Q : Subgroup ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) (centralizer ({t} : Set X)) := ⟨Q, rfl⟩
  have hES : E ≤ (Q : Subgroup ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype := fun x hx => ⟨⟨x, hEH hx⟩, hQ hx, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgen, -⟩ := h.lemma41 hKG hS
  obtain ⟨s, hs, hsE⟩ := hgen E hES
  calc Nat.card E = Nat.card (closure (s : Set X)) := by rw [hsE]
    _ ≤ 2 ^ s.card := RankFour.card_closure_le_two_pow s (by rw [hsE]; exact hE.1)
        (by rw [hsE]; exact hE.2)
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right two_pos hs

theorem card_le_sixteen_of_le_centralizer_bar (hKG : AutPSL2SylowInput) (h : Standing t L p f)
    {β : X} (htβ : t ∈ centralizer ({β} : Set X)) {E : Subgroup (MBar β)}
    (hEt : E ≤ centralizer {(QuotientGroup.mk ⟨t, htβ⟩ : MBar β)}) (hE : GrSLit.IsElemTwo E) :
    Nat.card E ≤ 16 := by
  set M := centralizer ({β} : Set X)
  set tt : ↥M := ⟨t, htβ⟩
  have ht2 : tt * tt = 1 := by
    have h1 : t * t = 1 := by rw [← sq, ← h.config.orderOf_eq, pow_orderOf_eq_one]
    exact Subtype.ext h1
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  let φ : ↥(centralizer ({tt} : Set ↥M)) →* MBar β :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (centralizer ({tt} : Set ↥M)).subtype
  have hrange : φ.range = centralizer {(QuotientGroup.mk tt : MBar β)} := by
    rw [MonoidHom.range_comp, range_subtype]
    exact map_centralizer_eq hodd ht2
  have hker : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map (centralizer ({tt} : Set ↥M)).subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (x : ↥M) = 1 := hx
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective (centralizer ({tt} : Set ↥M)).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨E', hE', -, hcard⟩ := RankFour.exists_isElemTwo_map_eq hker hE (hrange ▸ hEt)
  set E'' : Subgroup X := (E'.map (centralizer ({tt} : Set ↥M)).subtype).map M.subtype
  have hE''t : E'' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    have hx := mem_centralizer_singleton_iff.mp x.2
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx)
  have hcard'' : Nat.card E'' = Nat.card E' := by
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective (centralizer ({tt} : Set ↥M)).subtype_injective]
  rw [← hcard, ← hcard'']
  exact h.card_le_sixteen_of_isElemTwo hKG hE''t
    (RankFour.isElemTwo_map _ (RankFour.isElemTwo_map _ hE'))

end Standing

end CFSG.ComponentClassification.HarrisLit
