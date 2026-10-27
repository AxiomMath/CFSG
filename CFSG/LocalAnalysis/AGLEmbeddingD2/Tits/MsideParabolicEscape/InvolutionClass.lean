module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix (set_mul_eq_of_card)
open scoped Pointwise

theorem sylow_permute_of_involution_class
    {N : Type} [Group N] [Finite N] (hs : IsSimpleGroup N) (hnc : ¬ IsMulCommutative N)
    (hcard : Nat.card N = 6048)
    (hcnt : Nat.card {b : N // orderOf b = 2} = 63)
    (hconj : ∀ a b : N, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (Y : Subgroup (MulAut N)) (hY : innSub N ≤ Y) (h2 : (innSub N).relIndex Y ≤ 2)
    (S : Subgroup (MulAut N)) (hS : IsSylowTwoOf S Y) :
    ∃ P : Subgroup (MulAut N), P ≤ innSub N ∧ Nat.card P = 3 ∧
      (S : Set (MulAut N)) * P = (P : Set (MulAut N)) * S := by
  haveI : Finite (MulAut N) := inferInstance
  have hinj := conj_injective_of_simple hs hnc
  obtain ⟨hSY, hS2, hSi⟩ := hS
  have hr0 : (innSub N).relIndex Y ≠ 0 := by
    have h := Subgroup.relIndex_mul_card (H := innSub N) (K := Y)
    intro h0
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥Y)).ne' h.symm
  have hcinn : Nat.card (innSub N) = 6048 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hYcard : Nat.card Y = (innSub N).relIndex Y * 6048 := by
    have h := Subgroup.relIndex_mul_card (H := innSub N) (K := Y)
    rw [inf_of_le_left hY, hcinn] at h
    exact h.symm
  set r := (innSub N).relIndex Y with hr
  have hr12 : r = 1 ∨ r = 2 := by omega
  obtain ⟨b₀, hb₀⟩ : ∃ b : N, orderOf b = 2 := by
    have : Nonempty {b : N // orderOf b = 2} := Nat.card_pos_iff.mp (by omega) |>.1
    obtain ⟨⟨b, hb⟩⟩ := this
    exact ⟨b, hb⟩
  set Ω := MulAction.orbit (↥Y) b₀ with hΩdef
  have hΩset : (Ω : Set N) = {b | orderOf b = 2} := by
    ext b
    constructor
    · rintro ⟨σ, rfl⟩
      show orderOf ((σ : MulAut N) b₀) = 2
      rw [MulEquiv.orderOf_eq]
      exact hb₀
    · intro hb
      obtain ⟨c, hc⟩ := isConj_iff.mp (hconj b₀ b hb₀ hb)
      refine ⟨⟨MulAut.conj c, hY ⟨c, rfl⟩⟩, ?_⟩
      show (MulAut.conj c : MulAut N) b₀ = b
      rw [MulAut.conj_apply]
      exact hc
  have hΩcard : Nat.card Ω = 63 := by
    rw [← hcnt]
    show Nat.card ↥(Ω : Set N) = Nat.card ↥{b : N | orderOf b = 2}
    rw [hΩset]
  set S' : Subgroup ↥Y := S.subgroupOf Y with hS'
  have hS'2 : IsPGroup 2 ↥S' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
  have hmod := IsPGroup.card_modEq_card_fixedPoints (p := 2) (G := ↥S') (α := ↥Ω) hS'2
  rw [hΩcard] at hmod
  obtain ⟨ω, hωfix⟩ : ∃ ω : ↥Ω, ω ∈ MulAction.fixedPoints (↥S') ↥Ω := by
    by_contra hne
    have h0 : Nat.card (MulAction.fixedPoints (↥S') ↥Ω) = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨w, hw⟩ => hne ⟨w, hw⟩⟩
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨ω, hωΩ⟩ := ω
  have hfixS : ∀ s : MulAut N, ∀ hs : s ∈ S, (⟨s, hSY hs⟩ : ↥Y) • ω = ω := by
    intro s hs
    have := hωfix ⟨⟨s, hSY hs⟩, Subgroup.mem_subgroupOf.mpr hs⟩
    exact congrArg Subtype.val this
  have hωorb : MulAction.orbit (↥Y) ω = Ω := MulAction.orbit_eq_iff.mpr hωΩ
  set Stab : Subgroup ↥Y := MulAction.stabilizer (↥Y) ω with hStabdef
  have hidx : Stab.index = 63 := by
    rw [hStabdef, MulAction.index_stabilizer, hωorb]
    exact hΩcard
  have hStab : Nat.card Stab = 96 * r := by
    have h := Subgroup.card_mul_index Stab
    rw [hidx, hYcard] at h
    omega
  set H : Subgroup (MulAut N) := Stab.map Y.subtype with hH
  have hHcard : Nat.card H = 96 * r := by
    rw [hH, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hStab
  have hSH : S ≤ H := fun s hs => ⟨⟨s, hSY hs⟩, hfixS s hs, rfl⟩
  have hScard : Nat.card S = 32 * r := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hS2
    have h := Subgroup.card_mul_index S'
    have hS'c : Nat.card S' = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
    rw [hS'c, hn, hYcard] at h
    have hn13 : n ≤ 13 := by
      by_contra hc
      have hc : 14 ≤ n := by omega
      have h14 : 2 ^ 14 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
      have hi : 0 < S'.index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hSi)
      have : 2 ^ n ≤ 2 ^ n * S'.index := Nat.le_mul_of_pos_right _ hi
      omega
    rw [hn]
    interval_cases n <;> omega
  obtain ⟨P, hPH, hPcard⟩ : ∃ P : Subgroup (MulAut N), P ≤ H ∧ Nat.card P = 3 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 1)
      (by rw [hHcard]; exact ⟨32 * r, by ring⟩)
    refine ⟨K.map H.subtype, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
      norm_num
  have hSP : S ⊓ P = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (S ⊓ P : Subgroup (MulAut N)) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (S ⊓ P : Subgroup (MulAut N)) ∣ Nat.card P :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hPcard] at h2
    rw [hScard] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
    · exact h
    · rw [h] at h1
      omega
  have e1 : (S : Set (MulAut N)) * (P : Set (MulAut N)) = (H : Set (MulAut N)) :=
    set_mul_eq_of_card S P H hSH hPH hSP (by rw [hScard, hPcard, hHcard]; ring)
  have e2 : (P : Set (MulAut N)) * (S : Set (MulAut N)) = (H : Set (MulAut N)) :=
    set_mul_eq_of_card P S H hPH hSH (by rw [inf_comm]; exact hSP)
      (by rw [hScard, hPcard, hHcard]; ring)
  refine ⟨P, ?_, hPcard, by rw [e1, e2]⟩
  intro x hx
  have hxY : x ∈ Y := by
    obtain ⟨y, -, rfl⟩ := hPH hx
    exact y.2
  have hx3 : x ^ 3 = 1 := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : P)
    rw [hPcard] at h
    have h' := orderOf_dvd_iff_pow_eq_one.mp h
    exact congrArg Subtype.val h'
  rcases hr12 with h1 | h1
  · have h1' : (innSub N).relIndex Y = 1 := by rw [← hr]; exact h1
    exact (Subgroup.relIndex_eq_one.mp h1') hxY
  · have hK : ((innSub N).subgroupOf Y).index = 2 := by
      show (innSub N).relIndex Y = 2
      rw [← hr]
      exact h1
    have hy3 : (⟨x, hxY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext hx3
    have hmem := Subgroup.sq_mem_of_index_two hK ((⟨x, hxY⟩ : ↥Y) ^ 2)
    have heq : ((⟨x, hxY⟩ : ↥Y) ^ 2) ^ 2 = ⟨x, hxY⟩ := by
      calc ((⟨x, hxY⟩ : ↥Y) ^ 2) ^ 2 = (⟨x, hxY⟩ : ↥Y) * (⟨x, hxY⟩ : ↥Y) ^ 3 := by group
        _ = ⟨x, hxY⟩ := by rw [hy3, mul_one]
    rw [heq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
