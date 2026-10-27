module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_inv (h b : G) (n : ℕ) : (h⁻¹ * b * h) ^ n = h⁻¹ * b ^ n * h := by
  have := conj_pow (a := h⁻¹) (b := b) (i := n)
  simpa using this

theorem exists_conj_le_of_isSylowOf {K P Q : Subgroup G} (hP : IsSylowOf 2 P K) (hQK : Q ≤ K)
    (hQ : IsPGroup 2 Q) : ∃ c ∈ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R P₀
  refine ⟨c, c.2, fun q hq => ?_⟩
  have h1 : MulAut.conj c • (⟨q, hQK hq⟩ : K) ∈ MulAut.conj c • (R : Subgroup K) :=
    smul_mem_pointwise_smul _ (MulAut.conj c) (R : Subgroup K) (hR (mem_subgroupOf.mpr hq))
  rw [← Sylow.coe_subgroup_smul, hc, hP₀, mem_subgroupOf] at h1
  exact h1

theorem exists_conj_eq_of_isSylowOf {K P P' : Subgroup G} (hP : IsSylowOf 2 P K)
    (hP' : IsSylowOf 2 P' K) : ∃ c ∈ K, ∀ x : G, x ∈ P' ↔ c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_isSylowOf hP hP'.le hP'.isPGroup
  have hle : P'.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact hc q hq
  have heq : P'.map (MulAut.conj c).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj c).injective, hP.card_eq, hP'.card_eq])
  refine ⟨c, hcK, fun x => ⟨fun hx => hc x hx, fun hx => ?_⟩⟩
  rw [← heq] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  have : q = x := by
    have h := congrArg (fun y => c⁻¹ * y * c) hqx
    simpa [mul_assoc] using h
  rwa [← this]

theorem exists_conj_extremal {S : Subgroup G} (hS : IsPGroup 2 S) {u v h : G}
    (hv : IsSylowOf 2 (S ⊓ centralizer ({v} : Set G)) (centralizer ({v} : Set G)))
    (huv : h⁻¹ * v * h = u) :
    ∃ g : G, g⁻¹ * u * g = v ∧ ∀ c ∈ S ⊓ centralizer ({u} : Set G),
      g⁻¹ * c * g ∈ S ⊓ centralizer ({v} : Set G) := by
  set P := S ⊓ centralizer ({u} : Set G)
  set P' := P.map (MulAut.conj h).toMonoidHom
  have hP'K : P' ≤ centralizer ({v} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    rw [mem_centralizer_singleton_iff]
    change h * c * h⁻¹ * v = v * (h * c * h⁻¹)
    have hv' : v = h * u * h⁻¹ := by rw [← huv]; group
    rw [hv']
    calc h * c * h⁻¹ * (h * u * h⁻¹) = h * (c * u) * h⁻¹ := by group
      _ = h * (u * c) * h⁻¹ := by rw [hcu]
      _ = h * u * h⁻¹ * (h * c * h⁻¹) := by group
  have hP' : IsPGroup 2 P' := (hS.to_le inf_le_left).map _
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_isSylowOf hv hP'K hP'
  refine ⟨h⁻¹ * c⁻¹, ?_, fun x hx => ?_⟩
  · have hcv : c * v = v * c := mem_centralizer_singleton_iff.mp hcK
    rw [← huv]
    calc (h⁻¹ * c⁻¹)⁻¹ * (h⁻¹ * v * h) * (h⁻¹ * c⁻¹) = c * v * c⁻¹ := by group
      _ = v := by rw [hcv]; group
  · have := hc (h * x * h⁻¹) ⟨x, hx, rfl⟩
    rwa [show c * (h * x * h⁻¹) * c⁻¹ = (h⁻¹ * c⁻¹)⁻¹ * x * (h⁻¹ * c⁻¹) by group] at this

theorem isSylowOf_inf_centralizer_of_le {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {z : G}
    (hz : S ≤ centralizer ({z} : Set G)) :
    IsSylowOf 2 (S ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inf_of_le_left hz]
  exact hS.of_le hz le_top

theorem isSylowOf_top (P : Sylow 2 G) : IsSylowOf 2 (P : Subgroup G) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card le_top ?_
  rw [Sylow.card_eq_multiplicity, card_top]

theorem isSylowOf_of_card_le {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {u : G} (hu : u ∈ S)
    (hmax : ∀ g : G, g⁻¹ * u * g ∈ S →
      Nat.card ↥(S ⊓ centralizer ({g⁻¹ * u * g} : Set G)) ≤
        Nat.card ↥(S ⊓ centralizer ({u} : Set G))) :
    IsSylowOf 2 (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set G)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 C
  have huC : u ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have huP : u ∈ P := by
    have h2 : IsPGroup 2 (zpowers u) := hS.isPGroup.to_le (zpowers_le.mpr hu)
    have hle : zpowers u ≤ normalizer (P : Set G) := by
      rw [zpowers_le]
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun p hp => ?_)
      exact mem_centralizer_singleton_iff.mp (hP.le hp)
    have hsup : IsPGroup 2 (P ⊔ zpowers u : Subgroup G) := hP.isPGroup.to_sup_of_normal_left' h2 hle
    have heq := hP.eq_of_le le_sup_left (sup_le hP.le (zpowers_le.mpr huC)) hsup
    rw [← heq]
    exact mem_sup_right (mem_zpowers u)
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hS le_top hP.isPGroup
  have hw : c⁻¹⁻¹ * u * c⁻¹ ∈ S := by rw [inv_inv]; exact hc u huP
  have h1 := hmax c⁻¹ hw
  rw [inv_inv] at h1
  have hmapP : P.map (MulAut.conj c).toMonoidHom ≤ S ⊓ centralizer ({c * u * c⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.mpr ⟨hc q hq, mem_centralizer_singleton_iff.mpr ?_⟩
    have hqu : q * u = u * q := mem_centralizer_singleton_iff.mp (hP.le hq)
    change c * q * c⁻¹ * (c * u * c⁻¹) = c * u * c⁻¹ * (c * q * c⁻¹)
    calc c * q * c⁻¹ * (c * u * c⁻¹) = c * (q * u) * c⁻¹ := by group
      _ = c * (u * q) * c⁻¹ := by rw [hqu]
      _ = c * u * c⁻¹ * (c * q * c⁻¹) := by group
  have hge : Nat.card P ≤ Nat.card ↥(S ⊓ C) := by
    calc Nat.card P = Nat.card ↥(P.map (MulAut.conj c).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj c).injective).symm
      _ ≤ _ := card_le_of_le hmapP
      _ ≤ _ := h1
  obtain ⟨c', -, hc'⟩ := exists_conj_le_of_isSylowOf hP (inf_le_right : S ⊓ C ≤ C)
    (hS.isPGroup.to_le inf_le_left)
  have hle : Nat.card ↥(S ⊓ C) ≤ Nat.card P := by
    calc Nat.card ↥(S ⊓ C) = Nat.card ↥((S ⊓ C).map (MulAut.conj c').toMonoidHom) :=
          (card_map_of_injective (MulAut.conj c').injective).symm
      _ ≤ Nat.card P := card_le_of_le (by rintro _ ⟨q, hq, rfl⟩; exact hc' q hq)
  exact isSylowOf_of_card inf_le_right (by rw [← hP.card_eq]; omega)

theorem exists_mul_mem_normalizer {H N P : Subgroup G} (hHN : H ≤ normalizer (N : Set G))
    (hP : IsSylowOf 2 P N) {u : G} (hu : u ∈ H) : ∃ c ∈ N, u * c ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P'' := P.map (MulAut.conj u⁻¹).toMonoidHom
  have hu' : u⁻¹ ∈ normalizer (N : Set G) := inv_mem (hHN hu)
  have hP''N : P'' ≤ N := by
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_normalizer_iff.mp hu' p).mp (hP.le hp)
  have hP'' : IsSylowOf 2 P'' N :=
    isSylowOf_of_card hP''N (by rw [card_map_of_injective (MulAut.conj u⁻¹).injective, hP.card_eq])
  obtain ⟨c', hc'N, hc'⟩ := exists_conj_eq_of_isSylowOf hP hP''
  refine ⟨c'⁻¹, inv_mem hc'N, mem_normalizer_iff.mpr fun x => ?_⟩
  have key : ∀ y : G, y ∈ P'' ↔ u * y * u⁻¹ ∈ P := by
    intro y
    constructor
    · rintro ⟨p, hp, rfl⟩
      change u * (u⁻¹ * p * u⁻¹⁻¹) * u⁻¹ ∈ P
      rwa [show u * (u⁻¹ * p * u⁻¹⁻¹) * u⁻¹ = p by group]
    · intro hy
      exact ⟨u * y * u⁻¹, hy, by change u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y; group⟩
  rw [show u * c'⁻¹ * x * (u * c'⁻¹)⁻¹ = u * (c'⁻¹ * x * c') * u⁻¹ by group, ← key,
    hc', show c' * (c'⁻¹ * x * c') * c'⁻¹ = x by group]

end CFSG.ComponentClassification.GHarris
