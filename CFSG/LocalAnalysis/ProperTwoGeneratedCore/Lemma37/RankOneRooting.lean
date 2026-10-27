module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderRooting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneNormal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneQuaternion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

@[expose] noncomputable def liftToSylow (hz : IsCentralInvolution (S : Subgroup G) z)
    (X : Subgroup (EscapingQuotient z)) : Subgroup G :=
  (X.comap (sylowBar hz)).map (S : Subgroup G).subtype

omit [Finite G] in
theorem mem_liftToSylow (hz : IsCentralInvolution (S : Subgroup G) z)
    {X : Subgroup (EscapingQuotient z)} {g : G} :
    g ∈ liftToSylow hz X ↔ ∃ hg : g ∈ (S : Subgroup G), sylowBar hz ⟨g, hg⟩ ∈ X := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hg, hgX⟩
    exact ⟨⟨g, hg⟩, hgX, rfl⟩

omit [Finite G] in
theorem liftToSylow_le (hz : IsCentralInvolution (S : Subgroup G) z)
    (X : Subgroup (EscapingQuotient z)) : liftToSylow hz X ≤ (S : Subgroup G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_liftToSylow_iff (hz : IsCentralInvolution (S : Subgroup G) z)
    {X : Subgroup (EscapingQuotient z)} (s : (S : Subgroup G)) :
    (s : G) ∈ liftToSylow hz X ↔ sylowBar hz s ∈ X := by
  rw [mem_liftToSylow]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨s.2, h⟩⟩

omit [Finite G] in
theorem exists_sylowBar_eq (hz : IsCentralInvolution (S : Subgroup G) z)
    {x : EscapingQuotient z} (hx : x ∈ escapingSylowImage S z) :
    ∃ s : (S : Subgroup G), sylowBar hz s = x := by
  rw [← sylowBar_range hz] at hx
  exact hx

theorem orderOf_sylowBar (hz : IsCentralInvolution (S : Subgroup G) z)
    (s : (S : Subgroup G)) : orderOf (sylowBar hz s) = orderOf (s : G) := by
  rw [orderOf_injective _ (sylowBar_injective hz), Subgroup.orderOf_coe]

theorem sylowBar_eq_bar_iff (hz : IsCentralInvolution (S : Subgroup G) z)
    (s : (S : Subgroup G)) : sylowBar hz s = escapingBar z ↔ (s : G) = z := by
  rw [← sylowBar_self hz]
  constructor
  · intro h1
    exact congrArg Subtype.val (sylowBar_injective hz h1)
  · intro h1
    rw [show s = ⟨z, hz.1⟩ from Subtype.ext h1]

variable {H : Subgroup G} {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

theorem false_of_sylowImage_le_sup
    (hle : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    False := by
  have hz := h.square.central
  set K := Subgroup.centralizer (J : Set (EscapingQuotient z)) with hK
  set A := liftToSylow hz (escapingSylowImage S z ⊓ J) with hA
  set B := liftToSylow hz (escapingSylowImage S z ⊓ K) with hB
  have hbar : ∀ s : (S : Subgroup G), sylowBar hz s ∈ escapingSylowImage S z := fun s => by
    rw [← sylowBar_range hz]
    exact ⟨s, rfl⟩
  refine coreSetting_rooting_central_product_false h.square.core hz (A := A) (B := B)
    (liftToSylow_le hz _) ?_ ?_ ?_ ?_ ?_
  ·
    intro s hs
    obtain ⟨q, hqS, hqJ, c, hcS, hcK, hqc⟩ := h.exists_mul_eq_of_mem_sup (hbar ⟨s, hs⟩)
      (hle (hbar ⟨s, hs⟩))
    obtain ⟨a, rfl⟩ := exists_sylowBar_eq hz hqS
    obtain ⟨b, rfl⟩ := exists_sylowBar_eq hz hcS
    refine ⟨a, (mem_liftToSylow_iff hz a).mpr ⟨hqS, hqJ⟩, b,
      (mem_liftToSylow_iff hz b).mpr ⟨hcS, hcK⟩, ?_⟩
    rw [← map_mul] at hqc
    exact congrArg Subtype.val (sylowBar_injective hz hqc)
  ·
    intro a ha b hb
    obtain ⟨has, haJ⟩ := (mem_liftToSylow hz).mp ha
    obtain ⟨hbs, hbK⟩ := (mem_liftToSylow hz).mp hb
    exact commute_of_sylowBar hz (s := ⟨a, has⟩) (t := ⟨b, hbs⟩)
      (Subgroup.mem_centralizer_iff.mp hbK.2 _ haJ.2)
  ·
    intro a ha ha2
    obtain ⟨has, haJ⟩ := (mem_liftToSylow hz).mp ha
    rw [← sylowBar_eq_bar_iff hz ⟨a, has⟩]
    exact h.unique _ haJ.2 (by rw [orderOf_sylowBar]; exact ha2)
  ·
    intro b hb hb2
    obtain ⟨hbs, hbK⟩ := (mem_liftToSylow hz).mp hb
    rw [← sylowBar_eq_bar_iff hz ⟨b, hbs⟩]
    exact h.eq_bar_of_mem_centralizer hbK.1 hbK.2 (by rw [orderOf_sylowBar]; exact hb2)
  ·
    intro a ha
    obtain ⟨has, haJ⟩ := (mem_liftToSylow hz).mp ha
    have h4 := h.pow_four_eq_one haJ.1 haJ.2
    rw [← map_pow, ← map_one (sylowBar hz)] at h4
    exact congrArg Subtype.val (sylowBar_injective hz h4)

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
