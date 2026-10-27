module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem card_le_card_sylow_of_isPGroup (S : Sylow 2 J) {P : Subgroup J} (hP : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card (S : Subgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  calc Nat.card P ≤ Nat.card (S' : Subgroup J) := Subgroup.card_le_of_le hS'
    _ = Nat.card (S : Subgroup J) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

theorem isPGroup_zpowers_of_orderOf_eq_four {G : Type*} [Group G] {x : G} (hx : orderOf x = 4) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)

namespace FourGen

theorem relIndex_centralizer_eq_two (hz : FourGen Q z) (h : Setting J Q B) {q₀ : J}
    (hq₀Q : q₀ ∈ (Q : Subgroup J)) (hq₀ : q₀ * z * q₀⁻¹ = centralElt J * z) :
    ((Q : Subgroup J) ⊓ Subgroup.centralizer ({z} : Set J)).relIndex (Q : Subgroup J) = 2 := by
  have hne : centralElt J * z ≠ z := fun h' => h.centralElt_ne_one (mul_eq_right.mp h')
  have hmemC : ∀ b : (Q : Subgroup J), b ∈ ((Q : Subgroup J) ⊓
      Subgroup.centralizer ({z} : Set J)).subgroupOf (Q : Subgroup J) ↔
        (b : J) * z * (b : J)⁻¹ = z := fun b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hb⟩
      rw [hb, mul_inv_cancel_right]
    · intro hb
      refine ⟨b.2, ?_⟩
      calc (b : J) * z = (b : J) * z * (b : J)⁻¹ * b := by group
        _ = z * b := by rw [hb]
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨q₀, hq₀Q⟩, fun b => ?_⟩
  rw [hmemC, hmemC]
  have hbq : ((b * ⟨q₀, hq₀Q⟩ : (Q : Subgroup J)) : J) * z *
      ((b * ⟨q₀, hq₀Q⟩ : (Q : Subgroup J)) : J)⁻¹ = centralElt J * ((b : J) * z * (b : J)⁻¹) := by
    calc ((b * ⟨q₀, hq₀Q⟩ : (Q : Subgroup J)) : J) * z *
          ((b * ⟨q₀, hq₀Q⟩ : (Q : Subgroup J)) : J)⁻¹ = (b : J) * (q₀ * z * q₀⁻¹) * (b : J)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
      _ = centralElt J * ((b : J) * z * (b : J)⁻¹) := by
          rw [hq₀, ← mul_assoc, (h.commute_centralElt (b : J)).eq, mul_assoc, mul_assoc,
            mul_assoc]
  rw [hbq]
  rcases hz.conj_eq h b.2 with h1 | h1 <;> rw [h1]
  · exact Or.inr ⟨rfl, hne⟩
  · rw [← mul_assoc, h.centralElt_mul_self, one_mul]
    exact Or.inl ⟨rfl, hne⟩

theorem exists_conj_commute (hz : FourGen Q z) (h : Setting J Q B) (hu : u * u = centralElt J) :
    ∃ g : J, g⁻¹ * u * g ∈ (Q : Subgroup J) ∧ g⁻¹ * u * g * z = z * (g⁻¹ * u * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hCQ : ∀ q ∈ (Q : Subgroup J), q * z = z * q
  · obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q
      (isPGroup_zpowers_of_orderOf_eq_four (h.orderOf_eq_four hu))
    have hgQ := hg u (Subgroup.mem_zpowers u)
    exact ⟨g, hgQ, hCQ _ hgQ⟩
  push Not at hCQ
  obtain ⟨q₀, hq₀Q, hq₀z⟩ := hCQ
  have hq₀ : q₀ * z * q₀⁻¹ = centralElt J * z := (hz.conj_eq h hq₀Q).resolve_left fun h1 =>
    hq₀z (by
      calc q₀ * z = q₀ * z * q₀⁻¹ * q₀ := by group
        _ = z * q₀ := by rw [h1])
  set C := (Q : Subgroup J) ⊓ Subgroup.centralizer ({z} : Set J) with hC
  have hrel : C.relIndex (Q : Subgroup J) = 2 := hz.relIndex_centralizer_eq_two h hq₀Q hq₀
  have hker : (QuotientGroup.mk' (Subgroup.center J)).ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact le_inf h.center_le_sylow fun c hc =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc z).symm
  have hperf : commutator (J ⧸ Subgroup.center J) = ⊤ := by
    have := h.perfect
    exact Group.IsPerfect.commutator_eq_top
  set Qbar := Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) with hQbar
  have hCQbar : C.map (QuotientGroup.mk' (Subgroup.center J)) ≤ (Qbar : Subgroup _) := by
    rw [hQbar, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono inf_le_left
  have hrelbar : (C.map (QuotientGroup.mk' (Subgroup.center J))).relIndex
      (Qbar : Subgroup _) = 2 := by
    rw [hQbar, Sylow.coe_mapSurjective, ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self hker]
    exact hrel
  have hubar : orderOf (u : J ⧸ Subgroup.center J) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hu, QuotientGroup.eq_one_iff]
      exact h.centralElt_mem_center
    · rw [Ne, QuotientGroup.eq_one_iff]
      intro huZ
      have := h.mul_self_of_mem_center huZ
      rw [hu] at this
      exact h.centralElt_ne_one this
  obtain ⟨gbar, hg⟩ := exists_conj_mem_of_relIndex_eq_two hperf Qbar hCQbar hrelbar hubar
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gbar
  have hmem : g⁻¹ * u * g ∈ C := by
    rw [← Subgroup.comap_map_eq_self hker, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hg
  exact ⟨g, hmem.1, Subgroup.mem_centralizer_singleton_iff.mp hmem.2⟩

end FourGen

theorem EscapingLift.exists_mem_inv_mul_mem (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) {g : J} (hg : g * z * g⁻¹ ∈ quasiNormalizer u) :
    ∃ c ∈ quasiNormalizer u, c⁻¹ * g ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, -, -⟩ := hu.exists_sylow h hz
  have hord : orderOf (g * z * g⁻¹) = 2 := by
    have := (MulAut.conj g).orderOf_eq z
    simp only [MulAut.conj_apply] at this
    rw [this, hz.order]
  have hy2 : IsPGroup 2 (Subgroup.zpowers (⟨g * z * g⁻¹, hg⟩ : quasiNormalizer u)) :=
    isPGroup_zpowers_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk]; exact hord)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow T hy2
  have hcB := Subgroup.mem_subgroupOf.mp (hT (hc _ (Subgroup.mem_zpowers _)))
  refine ⟨c, c.2, h.mem_of_conj_mem (hz.mem_of_setting h) hz.order hz.not_mem_center ?_⟩
  have heq : (c : J)⁻¹ * g * z * ((c : J)⁻¹ * g)⁻¹ =
      ((c⁻¹ * ⟨g * z * g⁻¹, hg⟩ * c : quasiNormalizer u) : J) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [heq]
  exact hcB

namespace FourGen

theorem exists_sylowPlaced (hz : FourGen Q z) (h : Setting J Q B) {w : J}
    (hwQ : w ∈ (Q : Subgroup J)) (hw : w * w = centralElt J) (hwz : w * z = z * w) :
    ∃ n ∈ Subgroup.normalizer (fourGroup z : Set J), n⁻¹ * w * n ∈ (Q : Subgroup J) ∧
      n⁻¹ * w * n * z = z * (n⁻¹ * w * n) ∧
      ∀ P ≤ Subgroup.normalizer (fourGroup z : Set J) ⊓ quasiNormalizer (n⁻¹ * w * n),
        IsPGroup 2 P →
          Nat.card P ≤ Nat.card ((Q : Subgroup J) ⊓ quasiNormalizer (n⁻¹ * w * n) :
            Subgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NV := Subgroup.normalizer (fourGroup z : Set J) with hNV
  have hQNV : (Q : Subgroup J) ≤ NV := hz.le_normalizer_fourGroup h
  set M₁ := NV ⊓ quasiNormalizer w with hM₁
  have hwM : w ∈ M₁ := ⟨hQNV hwQ, Subgroup.le_normalizer (Subgroup.mem_zpowers w)⟩
  have hw2 : IsPGroup 2 (Subgroup.zpowers (⟨w, hwM⟩ : M₁)) :=
    isPGroup_zpowers_of_orderOf_eq_four (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_four hw)
  obtain ⟨P₁, hwP₁⟩ := hw2.exists_le_sylow
  set P := (P₁ : Subgroup M₁).map M₁.subtype with hP
  have hwP : w ∈ P := ⟨⟨w, hwM⟩, hwP₁ (Subgroup.mem_zpowers _), rfl⟩
  have hPM : P ≤ M₁ := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := P₁.isPGroup'.map _
  have hPcard : Nat.card P = Nat.card (P₁ : Subgroup M₁) :=
    Subgroup.card_map_of_injective M₁.subtype_injective
  have hPmax : ∀ P' ≤ M₁, IsPGroup 2 P' → Nat.card P' ≤ Nat.card P := fun P' hP' hP'2 => by
    rw [hPcard]
    exact card_le_card_sylow_of_le P₁ hP' hP'2
  have hQmax : ∀ P' ≤ NV, IsPGroup 2 P' → Nat.card P' ≤ Nat.card (Q : Subgroup J) :=
    fun P' _ hP' => card_le_card_sylow_of_isPGroup Q hP'
  obtain ⟨n, hnNV, hn⟩ :=
    exists_conj_mem_of_card_le hQNV Q.isPGroup' hQmax (hPM.trans inf_le_left) hP2
  refine ⟨n, hnNV, hn w hwP, ?_, ?_⟩
  · have hwc : w * (n * z * n⁻¹) = (n * z * n⁻¹) * w := by
      rcases hz.conj_eq_of_mem_normalizer h hnNV with h1 | h1 <;> rw [h1]
      · exact hwz
      · rw [← mul_assoc, (h.commute_centralElt w).eq, mul_assoc, hwz, ← mul_assoc]
    calc n⁻¹ * w * n * z = n⁻¹ * (w * (n * z * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * z * n⁻¹) * w) * n := by rw [hwc]
      _ = z * (n⁻¹ * w * n) := by group
  · intro P' hP' hP'2
    have h1 : P'.map (MulAut.conj n).toMonoidHom ≤ M₁ := by
      rintro _ ⟨p, hp, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact ⟨NV.mul_mem (NV.mul_mem hnNV (hP' hp).1) (NV.inv_mem hnNV),
        (h.mem_quasiNormalizer_conj_iff hw n p).mp (hP' hp).2⟩
    have h2 : P.map (MulAut.conj n⁻¹).toMonoidHom ≤
        (Q : Subgroup J) ⊓ quasiNormalizer (n⁻¹ * w * n) := by
      rintro _ ⟨p, hp, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine ⟨hn p hp, (h.mem_quasiNormalizer_conj_iff hw n _).mpr ?_⟩
      rw [show n * (n⁻¹ * p * n) * n⁻¹ = p by group]
      exact (hPM hp).2
    calc Nat.card P' = Nat.card (P'.map (MulAut.conj n).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj n).injective).symm
      _ ≤ Nat.card P := hPmax _ h1 (hP'2.map _)
      _ = Nat.card (P.map (MulAut.conj n⁻¹).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le h2

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
