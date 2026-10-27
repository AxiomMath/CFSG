module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

namespace Sec3

namespace SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

theorem sqMap_eq_zero_of_conj_mem
    (hS : SzR G L T R a y d) {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) {x g : G} (hx : x ∈ R)
    (hg : g * x * g⁻¹ ∈ gmsA L T) : VLike.sqMap a c e (φ x) = 0 := by
  have h1 := (hS.facts.sylow hS.sec3).2.1 _ hg
  have hx2 : x ^ 2 = 1 := by
    have e : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by rw [sq, sq]; group
    rw [e, h1]
    group
  rw [← hC.sq x hx, hx2]
  have h2 := hC.v_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h2
  linear_combination -h2

theorem snd_ne_zero_of_conj_mem
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) {x g : G} (hx : x ∈ R) (hxA : x ∉ gmsA L T)
    (hg : g * x * g⁻¹ ∈ gmsA L T) : (φ x).2.1 ≠ 0 := by
  intro h0
  have hx2 : x ^ 2 = 1 := by
    have e : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by rw [sq, sq]; group
    rw [e, (hS.facts.sylow hS.sec3).2.1 _ hg]
    group
  obtain ⟨t, ht, r, hr, s, hs, rfl⟩ := hS.exists_decomp h34 hR₂ hx
  have htR := hS.T_le (mem_inf.mp ht).1
  have hrR := hR₂.le_R hr
  have hsR := hS.T_le (mem_inf.mp hs).1
  rw [hC.mul _ (mul_mem htR hrR) _ hsR, hC.mul _ htR _ hrR] at h0
  simp only [Prod.snd_add, Prod.fst_add] at h0
  rw [(hC.of_T₁ t ht).1, (hC.of_T₀ s hs).2, zero_add, add_zero] at h0
  have hrA : r ∈ gmsA L T :=
    (hC.ker r hrR).mp (Prod.ext (hC.of_R₂ r hr).1 (Prod.ext h0 (hC.of_R₂ r hr).2))
  have hxW : t * r * s ∈ gmsW L T := by
    rw [← hS.eq_gmsW]
    exact mul_mem (mul_mem (mem_inf.mp ht).1 (gmsA_le_T hrA)) (mem_inf.mp hs).1
  have hxV := (hS.facts.vFacts hS.sec3 hS.foundation).2.2.2.2 _ hxW hx2
  have e : g⁻¹ * (g * (t * r * s) * g⁻¹) * g⁻¹⁻¹ = t * r * s := by group
  have h1 := hS.lemma313.stronglyClosed _ hg g⁻¹ (by rw [e]; exact hxV)
  rw [e] at h1
  exact hxA h1

theorem closure_sqMap_ne_top_of_conj_mem
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G)
    {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) (hRG : IsSylowOf 2 R ⊤) {x g : G} (hx : x ∈ R)
    (hxA : x ∉ gmsA L T) (hg : g * x * g⁻¹ ∈ gmsA L T) :
    AddSubgroup.closure (VLike.sqMap a c e '' VLike.perp a c Λ (φ x)) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({x} : Set G) with hCdef
  set P := R.comap (MulAut.conj g).toMonoidHom with hP
  have hmemP : ∀ z, z ∈ P ↔ g * z * g⁻¹ ∈ R := fun z => Iff.rfl
  have hPC : P ≤ C := by
    intro z hz
    rw [hCdef, mem_centralizer_singleton_iff]
    have h1 := commute_of_mem_gmsTrans (hS.isR.le_gmsTrans ((hmemP z).mp hz)) hg
    calc z * x = g⁻¹ * (g * z * g⁻¹ * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
      _ = x * z := by group
  have hPG : IsSylowOf 2 P ⊤ := isSylowOf_of_card le_top
    ((Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun _ => Iff.rfl)).trans
      hRG.card_eq)
  obtain ⟨S, hSC, hRS⟩ := AS76b.exists_isSylowOf_le (inf_le_right : R ⊓ C ≤ C)
    (hRG.isPGroup.to_le inf_le_left)
  obtain ⟨k, hkC, hk⟩ := (hPG.of_le hPC le_top).exists_mem_conj hSC
  have hkx : k⁻¹ * x * k = x := by
    have h1 : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
    calc k⁻¹ * x * k = k⁻¹ * (k * x) := by rw [h1]; group
      _ = x := by group
  set h := g * k⁻¹ with hh
  have hhx : h * x * h⁻¹ ∈ gmsA L T := by
    have e : h * x * h⁻¹ = g * (k⁻¹ * x * k) * g⁻¹ := by rw [hh]; group
    rw [e, hkx]
    exact hg
  have hhz : ∀ z ∈ R ⊓ C, h * z * h⁻¹ ∈ R := by
    intro z hz
    have e : h * z * h⁻¹ = g * (k⁻¹ * z * k) * g⁻¹ := by rw [hh]; group
    rw [e]
    exact (hmemP _).mp ((hk z).mp (hRS hz))
  set A₁s := (gmsA L T).comap (MulAut.conj h).toMonoidHom with hA₁s
  have hmemA : ∀ z, z ∈ A₁s ↔ h * z * h⁻¹ ∈ gmsA L T := fun z => Iff.rfl
  obtain ⟨b₀, hb₀, hb₀s⟩ : ∃ b₀ ∈ gmsA L T, b₀ ∉ A₁s := by
    by_contra hcon
    push Not at hcon
    have hcard : Nat.card A₁s = Nat.card (gmsA L T) :=
      Nat.card_congr ((MulAut.conj h).toEquiv.subtypeEquiv fun _ => Iff.rfl)
    have heq : gmsA L T = A₁s := eq_of_le_of_card_ge (fun b hb => hcon b hb) hcard.le
    exact hxA (heq ▸ (hmemA x).mpr hhx)
  have hsqA : ∀ z ∈ R, z ^ 2 ∈ gmsA L T := fun z hz =>
    (hC.ker _ (pow_mem hz 2)).mp (by rw [sq, hC.mul z hz z hz]; exact CharTwo.add_self_eq_zero _)
  have hv1 : v 1 = 0 := by
    have h1 := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h1
    linear_combination -h1
  let B : AddSubgroup (BinaryGaloisField (2 * a + 1)) :=
    { carrier := v '' ((gmsA L T ⊓ A₁s : Subgroup G) : Set G)
      add_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', mul_mem hb hb', hC.v_mul b (mem_inf.mp hb).1 b' (mem_inf.mp hb').1⟩
      zero_mem' := ⟨1, one_mem _, hv1⟩
      neg_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b, hb, (CharTwo.neg_eq _).symm⟩ }
  have hsub : VLike.sqMap a c e '' VLike.perp a c Λ (φ x) ⊆ (B : Set _) := by
    rintro _ ⟨w, ⟨hwΛ, hw0⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hC.surj w hwΛ
    have h1 := hC.comm x hx z hz
    rw [hw0] at h1
    have hxz := hC.v_inj _ (hS.commutator_mem_gmsA h34 hx hz) h1
    have hzC : z ∈ R ⊓ C := by
      refine mem_inf.mpr ⟨hz, ?_⟩
      rw [hCdef, mem_centralizer_singleton_iff]
      calc z * x = x * z * x⁻¹ * z⁻¹ * (z * x) := by rw [hxz, one_mul]
        _ = x * z := by group
    have hz2 : z ^ 2 ∈ A₁s := by
      rw [hmemA]
      have e : h * z ^ 2 * h⁻¹ = (h * z * h⁻¹) ^ 2 := by rw [sq, sq]; group
      rw [e]
      exact hsqA _ (hhz z hzC)
    exact ⟨z ^ 2, mem_inf.mpr ⟨hsqA z hz, hz2⟩, hC.sq z hz⟩
  intro htop
  have hle := (AddSubgroup.closure_le B).mpr hsub
  rw [htop] at hle
  obtain ⟨b₁, hb₁, hvb⟩ := hle (AddSubgroup.mem_top (v b₀))
  obtain ⟨hb₁A, hb₁s⟩ := mem_inf.mp hb₁
  apply hb₀s
  have h1 := hC.v_mul b₀ hb₀ b₁ hb₁A
  rw [← hvb, CharTwo.add_self_eq_zero] at h1
  rw [eq_inv_of_mul_eq_one_left (hC.v_inj _ (mul_mem hb₀ hb₁A) h1)]
  exact inv_mem hb₁s

end SzR

end Sec3

theorem isSylowOf_top_of_isSylowOf_normalizer' {G : Type} [Group G] [Finite G]
    {R : Subgroup G} (hR : IsSylowOf 2 R (normalizer (R : Set G))) : IsSylowOf 2 R ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨S, hRS, z, hzS, hzN, hzR⟩ := exists_mem_normalizer_of_not_isSylowOf hR.isPGroup hnot
  have heq := hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hzN))
    (S.isPGroup'.to_le (sup_le hRS (zpowers_le.mpr hzS)))
  exact hzR (heq ▸ mem_sup_right (mem_zpowers z))

end CFSG.ComponentClassification.GMS78
