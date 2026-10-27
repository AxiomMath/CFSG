module

public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
import CFSG.HardMathSupport.Curtis.Proving.PerfectTwoThree

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect
  commutatorElement_mul_central commutator_self_le)

theorem isSmallTwoOrG2_iff (X : Type) [Group X] :
    IsSmallTwoOrG2 X ↔ IsSmallFourTwo X ∨ Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  unfold IsSmallTwoOrG2 IsSmallFourTwo
  constructor
  · rintro (⟨n, hn, e⟩ | ⟨d, hd, e⟩)
    · rcases hn with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨5, Or.inl rfl, e⟩)
      · exact Or.inl (Or.inl ⟨6, Or.inr rfl, e⟩)
      · exact Or.inr e
    · exact Or.inl (Or.inr ⟨d, hd, e⟩)
  · rintro ((⟨n, hn, e⟩ | ⟨d, hd, e⟩) | ⟨e⟩)
    · rcases hn with rfl | rfl
      · exact Or.inl ⟨5, Or.inl rfl, e⟩
      · exact Or.inl ⟨6, Or.inr (Or.inl rfl), e⟩
    · exact Or.inr ⟨d, hd, e⟩
    · exact Or.inl ⟨8, Or.inr (Or.inr rfl), e⟩

theorem mem_sup_of_commute_aux {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        simp only [mul_assoc]
        rw [← mul_assoc b₁, ← hc a₂ ha₂ b₁ hb₁, mul_assoc]
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [← mul_inv_rev, hc a ha b hb] }
  have hsup : A ⊔ B ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  obtain ⟨a, ha, b, hb, hgab⟩ := hsup hg
  exact ⟨a, ha, b, hb, hgab⟩

theorem top_of_mul_central_of_perfect {G : Type*} [Group G] (Z H : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) (hG : commutator G = ⊤)
    (hHZ : ∀ g : G, ∃ h ∈ H, ∃ z ∈ Z, g = h * z) : H = ⊤ := by
  have hG' : ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ := hG
  refine eq_top_iff.2 ?_
  rw [← hG']
  refine Subgroup.commutator_le.2 fun a _ b _ => ?_
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hHZ a
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hHZ b
  rw [commutatorElement_mul_central (hZ hz₁) (hZ hz₂)]
  exact commutator_self_le H (Subgroup.commutator_mem_commutator hh₁ hh₂)

theorem fixThreeVoid_smallFour :
    FixThreeVoid IsSmallFourTwo := by
  intro Y _ _ L J u h hX
  have hord : OvergroupOrder96 (↥L ⧸ Subgroup.center ↥L) := ordBound_isSmallFourTwo hX
  have hpar : IsParabolicTwo L J := h.parab.parab
  obtain ⟨hJL, T, hT, hTN⟩ := hpar
  have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hLperf : commutator ↥L = ⊤ := h.parab.comp.2.2.1
  have hJne : J ≠ L := h.parab.ne_top
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Jb : Subgroup ↥L := J.subgroupOf L with hJb
  have hJbne : Jb.map π ≠ ⊤ := by
    intro htop
    apply hJne
    have hHtop : Jb = ⊤ := by
      refine top_of_mul_central_of_perfect (Subgroup.center ↥L) Jb le_rfl hLperf ?_
      intro g
      have hg : π g ∈ Jb.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 hg
      exact ⟨h', hh', h'⁻¹ * g, QuotientGroup.eq.1 he, (mul_inv_cancel_left h' g).symm⟩
    rw [hJb, Subgroup.subgroupOf_eq_top] at hHtop
    exact le_antisymm hJL hHtop
  have hT₀ : IsSylowTwoOf ((T.subgroupOf L).map π) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) π hπs
  have hT₀J : (T.subgroupOf L).map π ≤ Jb.map π :=
    Subgroup.map_mono (fun x hx => hTJ hx)
  set V := perfectJoin J with hV
  have hVJ : V ≤ J := perfectJoin_le J
  have hVL : V ≤ L := hVJ.trans hJL
  have hVperf : ⁅V, V⁆ = V := perfectJoin_perfect J
  set C := Subgroup.centralizer (L : Set Y) with hC
  have hVC : ∀ a ∈ V, ∀ b ∈ C, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a (hVL ha)
  obtain ⟨v, hvV, c, hcC, huvc⟩ := mem_sup_of_commute_aux V C hVC h.join
  have hc' : c = v⁻¹ * u := by rw [huvc, inv_mul_cancel_left]
  have hvL : v ∈ L := hVL hvV
  have hcL : c ∈ L := hc' ▸ L.mul_mem (L.inv_mem hvL) h.mem
  have hcZ : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact Subgroup.mem_centralizer_iff.1 hcC _ g.2)
  have hπuv : π ⟨u, h.mem⟩ = π ⟨v, hvL⟩ := by
    apply QuotientGroup.eq.2
    have hmul : (⟨u, h.mem⟩ : ↥L)⁻¹ * ⟨v, hvL⟩ = (⟨c, hcL⟩ : ↥L)⁻¹ :=
      Subtype.ext (by
        show u⁻¹ * v = c⁻¹
        rw [hc', mul_inv_rev, inv_inv])
    rw [hmul]
    exact Subgroup.inv_mem _ hcZ
  set V' : Subgroup ↥L := V.subgroupOf L with hV'
  have hV'map : V'.map L.subtype = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVL hx⟩, hx, rfl⟩
  have hV'perf : ⁅V', V'⁆ = V' := by
    apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hV'map]
    exact hVperf
  set W : Subgroup (↥L ⧸ Subgroup.center ↥L) := V'.map π with hW
  have hWperf : ⁅W, W⁆ = W := by
    have h1 : (⁅V', V'⁆).map π = ⁅W, W⁆ := Subgroup.map_commutator V' V' π
    rw [hV'perf] at h1
    exact h1.symm
  have hWle : W ≤ Jb.map π :=
    Subgroup.map_mono (fun x hx => hVJ hx)
  have hWbot : W = ⊥ := by
    apply perfect_eq_bot_of_card_dvd_two_pow_mul_three (a := 5) W hWperf
    have hcard : Nat.card W ∣ Nat.card (Jb.map π) := Subgroup.card_dvd_of_le hWle
    have h96 : Nat.card (Jb.map π) ∣ 96 := hord _ _ hT₀ hT₀J hJbne
    exact hcard.trans (h96.trans (by norm_num))
  have hub : π ⟨u, h.mem⟩ ∈ W :=
    Subgroup.mem_map.2 ⟨⟨v, hvL⟩, hvV, hπuv.symm⟩
  rw [hWbot, Subgroup.mem_bot] at hub
  have huZ : (⟨u, h.mem⟩ : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 hub
  exact h.not_mem (Subgroup.mem_centralizer_iff.2 fun l hl => by
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 huZ ⟨l, hl⟩))

end CFSG.HardMathSupport.Curtis.Proving

end
