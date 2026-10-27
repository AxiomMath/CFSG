module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Swap

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P : Subgroup G} {e u : G} (Z : Subgroup G) [Z.Normal]

omit [Z.Normal] in
theorem central_le_of_caseB2 (hc : PartC T Q P e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) : Z ≤ T := by
  intro z hz
  rcases (hZ z).mp hz with rfl | rfl
  · exact T.one_mem
  · exact hc.left_le hc.mem_left

theorem mk_mem_map_iff_of_caseB2 (hc : PartC T Q P e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    (x : G) :
    (x : G ⧸ Z) ∈ T.map (QuotientGroup.mk' Z) ↔ x ∈ T := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hc.central_le_of_caseB2 Z hZ)]

theorem mem_inf_centralizer_iff_of_swap (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {x : G}
    (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ Q) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ P) (hxx : x * x ∈ T)
    {w : G ⧸ Z} :
    w ∈ T.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(x : G ⧸ Z)} ↔
      ∃ p ∈ P, w = ((p * (x * p * x⁻¹) : G) : G ⧸ Z) := by
  have hW : ∀ t ∈ T, (t : G ⧸ Z) ∈ T.map (QuotientGroup.mk' Z) := fun t ht => ⟨t, ht, rfl⟩
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, (a : G ⧸ Z) * (b : G ⧸ Z) = (b : G ⧸ Z) * (a : G ⧸ Z) :=
    fun a ha b hb => hc.comm_map_of_caseB2 Z hT φ hZ (hW a ha) (hW b hb)
  constructor
  · intro hw
    obtain ⟨⟨t, ht, rfl⟩, hxw⟩ := Subgroup.mem_inf.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply] at hxw
    rw [QuotientGroup.mk'_apply]
    obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hT ht)
    refine ⟨p, hp, ?_⟩
    have hconj : (((x * q * x⁻¹) * (x * p * x⁻¹) : G) : G ⧸ Z) = ((q * p : G) : G ⧸ Z) := by
      rw [← conj_mul_eq_mul_conj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hxw]
      group
    obtain ⟨z, hz, hzeq⟩ : ∃ z ∈ Z, q * p = (x * q * x⁻¹) * (x * p * x⁻¹) * z := by
      refine ⟨((x * q * x⁻¹) * (x * p * x⁻¹))⁻¹ * (q * p), QuotientGroup.eq.mp hconj, ?_⟩
      group
    have hab := hc.commute _ (hxP p hp) _ (hxQ q hq)
    have hzP : z ∈ P := by
      rcases (hZ z).mp hz with rfl | rfl
      · exact P.one_mem
      · exact hc.mem_right
    have hmem : (x * p * x⁻¹)⁻¹ * q ∈ Q ⊓ P := by
      refine ⟨Q.mul_mem (Q.inv_mem (hxP p hp)) hq, ?_⟩
      have h1 : (x * p * x⁻¹)⁻¹ * q = (x * q * x⁻¹) * z * p⁻¹ := by
        calc (x * p * x⁻¹)⁻¹ * q = (x * p * x⁻¹)⁻¹ * (q * p) * p⁻¹ := by group
          _ = (x * p * x⁻¹)⁻¹ * ((x * p * x⁻¹) * (x * q * x⁻¹) * z) * p⁻¹ := by
            rw [hzeq, ← hab]
          _ = (x * q * x⁻¹) * z * p⁻¹ := by group
      rw [h1]
      exact P.mul_mem (P.mul_mem (hxQ q hq) hzP) (P.inv_mem hp)
    have hqb : (q : G ⧸ Z) = ((x * p * x⁻¹ : G) : G ⧸ Z) := by
      refine (QuotientGroup.eq.mpr ?_).symm
      rw [hZ]
      exact hc.mem_inf _ hmem.1 hmem.2
    rw [QuotientGroup.mk_mul, hqb, ← QuotientGroup.mk_mul, hc.commute _ (hxP p hp) p hp]
  · rintro ⟨p, hp, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hW _ (T.mul_mem (hc.right_le hp) (hc.left_le (hxP p hp))), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcomm _ hxx _ (hc.right_le hp)
    have hB := hc.commute _ (hxP p hp) p hp
    have hB' : ((x * p * x⁻¹ : G) : G ⧸ Z) * (p : G ⧸ Z) =
        (p : G ⧸ Z) * ((x * p * x⁻¹ : G) : G ⧸ Z) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hB]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 hB' ⊢
    set X := (x : G ⧸ Z)
    set Pp := (p : G ⧸ Z)
    have key : X * (Pp * (X * Pp * X⁻¹)) * X⁻¹ = Pp * (X * Pp * X⁻¹) := by
      calc X * (Pp * (X * Pp * X⁻¹)) * X⁻¹ = X * Pp * X⁻¹ * (X * X * Pp * (X * X)⁻¹) := by group
        _ = X * Pp * X⁻¹ * Pp := by rw [h1, mul_inv_cancel_right]
        _ = Pp * (X * Pp * X⁻¹) := hB'
    calc Pp * (X * Pp * X⁻¹) * X = X * (Pp * (X * Pp * X⁻¹)) * X⁻¹ * X := by rw [key]
      _ = X * (Pp * (X * Pp * X⁻¹)) := by group

theorem card_inf_centralizer_of_swap (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (hZcard : Nat.card Z = 2)
    {x : G} (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ Q) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ P)
    (hxx : x * x ∈ T) :
    Nat.card (T.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(x : G ⧸ Z)} :
      Subgroup (G ⧸ Z)) = 4 := by
  let f : P →* G ⧸ Z :=
    { toFun := fun p => (((p : G) * (x * p * x⁻¹) : G) : G ⧸ Z)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul]
        congr 1
        change (a : G) * b * (x * (a * b) * x⁻¹) = _
        rw [conj_mul_eq_mul_conj, show (a : G) * b * (x * a * x⁻¹ * (x * b * x⁻¹)) =
          a * (b * (x * a * x⁻¹)) * (x * b * x⁻¹) by group,
          ← hc.commute _ (hxP a a.2) b b.2]
        group }
  have hrange : f.range = T.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(x : G ⧸ Z)} := by
    ext w
    rw [hc.mem_inf_centralizer_iff_of_swap Z hT φ hZ hxP hxQ hxx, MonoidHom.mem_range]
    exact ⟨fun ⟨p, hp⟩ => ⟨p, p.2, hp.symm⟩, fun ⟨p, hp, hw⟩ => ⟨⟨p, hp⟩, hw.symm⟩⟩
  have hZP : Z ≤ P := fun z hz => by
    rcases (hZ z).mp hz with rfl | rfl
    · exact P.one_mem
    · exact hc.mem_right
  have hker : f.ker = Z.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (((p : G) * (x * p * x⁻¹) : G) : G ⧸ Z) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have hpQ : (p : G) ∈ Q := by
        rw [show (p : G) = ((p : G) * (x * p * x⁻¹)) * (x * p * x⁻¹)⁻¹ by group]
        refine Q.mul_mem ?_ (Q.inv_mem (hxP p p.2))
        rcases (hZ _).mp h with h1 | h1
        · rw [h1]
          exact Q.one_mem
        · rw [h1]
          exact hc.mem_left
      exact (hZ _).mpr (hc.mem_inf _ hpQ p.2)
    · intro h
      rcases (hZ _).mp h with h1 | h1 <;> rw [h1]
      · simp
      · rw [hc.conj_centralElt x, hc.centralElt_mul_self]
        exact Z.one_mem
  have hcardP : Nat.card P = 8 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardK : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZcard]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hcardK, hcardP, hrange] at h
  omega

theorem le_normalizer_of_caseB2Normalized [Finite G] (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hn : CaseB2Normalized T P)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (hZcard : Nat.card Z = 2) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) :
    S ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hSN
  set S₀ := S ⊓ Subgroup.normalizer (T : Set G) with hS₀
  have hlt : S₀ < S := lt_of_le_of_ne inf_le_left (fun h => hSN (h ▸ inf_le_right))
  obtain ⟨E, hS₀E, -, hES⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension 2 S₀ S hS hlt
  obtain ⟨m, hmE, hmS₀⟩ := IsConcreteLE.exists_of_lt hS₀E
  have hmN : m ∈ Subgroup.normalizer (S₀ : Set G) := (hES hmE).2
  apply hmS₀
  refine ⟨(hES hmE).1, mem_normalizer_of_conj_mem fun t ht => ?_⟩
  by_contra hmt
  set W := T.map (QuotientGroup.mk' Z) with hWdef
  set X := (x : G ⧸ Z) with hXdef
  have hTS₀ : T ≤ S₀ := le_inf hTS Subgroup.le_normalizer
  have hconjS₀ : ∀ t ∈ T, m * t * m⁻¹ ∈ S₀ := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hmN t).mp (hTS₀ ht)
  have hswap := hc.swap_of_caseB2Normalized hT φ hn hS hTS hxS hxN hxT
  have hxx := hc.mul_self_mem_of_caseB2Normalized hT φ hn hS hTS hxS hxN hxT
  have hcard4 := hc.card_inf_centralizer_of_swap Z hT φ hZ hZcard hswap.1 hswap.2 hxx
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    hc.comm_map_of_caseB2 Z hT φ hZ ha hb
  set A := W.map (MulAut.conj (m : G ⧸ Z)).toMonoidHom with hAdef
  have hcardA : Nat.card A = 16 := by
    rw [hAdef, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hc.card_map_of_caseB2 Z hT φ hZ
  have hmk : ∀ t : G, (MulAut.conj (m : G ⧸ Z)).toMonoidHom (QuotientGroup.mk' Z t) =
      ((m * t * m⁻¹ : G) : G ⧸ Z) := fun t => by
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hA : ∀ b ∈ A, b ∈ W ∨ X⁻¹ * b ∈ W := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [hmk]
    rcases hc.mem_or_inv_mul_mem_of_caseB2Normalized hT φ hn hS hTS hxS hxN hxT
        (hconjS₀ t ht).1 (hconjS₀ t ht).2 with h | h
    · exact Or.inl ⟨_, h, rfl⟩
    · exact Or.inr ⟨_, h, by simp [hXdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hWcomm a ha b hb]
  have ha₀A : ((m * t * m⁻¹ : G) : G ⧸ Z) ∈ A := ⟨_, ⟨t, ht, rfl⟩, hmk t⟩
  have ha₀W : ((m * t * m⁻¹ : G) : G ⧸ Z) ∉ W := fun h =>
    hmt ((hc.mk_mem_map_iff_of_caseB2 Z hZ _).mp h)
  set a₀ := ((m * t * m⁻¹ : G) : G ⧸ Z) with ha₀def
  have hw₀ : X⁻¹ * a₀ ∈ W := (hA a₀ ha₀A).resolve_left ha₀W
  have hXW : ∀ w ∈ W, X * w * X⁻¹ ∈ W := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨x * t * x⁻¹, conj_mem_self_of_mem_normalizer hxN t ht,
      by simp [hXdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have hidx : W.relIndex A ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨a₀⁻¹, A.inv_mem ha₀A, fun b hb => ?_⟩
    rcases hA b hb with h | h
    · exact Or.inr h
    · left
      rw [show b * a₀⁻¹ = X * ((X⁻¹ * b) * (X⁻¹ * a₀)⁻¹) * X⁻¹ by group]
      exact hXW _ (W.mul_mem h (W.inv_mem hw₀))
  have hmul := Subgroup.relIndex_mul_card W A
  have h2 : W.relIndex A ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
  rw [hcardA] at hmul
  have hge : 8 ≤ Nat.card (W ⊓ A : Subgroup (G ⧸ Z)) := by nlinarith
  have hsub : W ⊓ A ≤ W ⊓ Subgroup.centralizer {X} := by
    intro c hcWA
    obtain ⟨hcW, hcA⟩ := Subgroup.mem_inf.mp hcWA
    refine Subgroup.mem_inf.mpr ⟨hcW, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hAcomm _ hcA _ ha₀A
    have h3 := hWcomm _ hcW _ hw₀
    calc c * X = c * a₀ * (X⁻¹ * a₀)⁻¹ := by group
      _ = a₀ * c * (X⁻¹ * a₀)⁻¹ := by rw [h1]
      _ = X * ((X⁻¹ * a₀) * c) * (X⁻¹ * a₀)⁻¹ := by group
      _ = X * (c * (X⁻¹ * a₀)) * (X⁻¹ * a₀)⁻¹ := by rw [h3]
      _ = X * c := by group
  have hle := Subgroup.card_le_of_le hsub
  change Nat.card (W ⊓ Subgroup.centralizer {X} : Subgroup (G ⧸ Z)) = 4 at hcard4
  omega

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
