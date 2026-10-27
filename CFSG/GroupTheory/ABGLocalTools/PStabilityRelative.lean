module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

open Subgroup

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem le_normalizer_of_le_of_sup_normal {P R : Subgroup H} (hR : IsPGroup p R) (hPR : P ≤ R)
    (hn : (pPrimeCore p H ⊔ P).Normal) : R ≤ normalizer (P : Set H) := by
  have hPp : IsPGroup p P := hR.to_le hPR
  have hsyl : IsSylowOf p P (pPrimeCore p H ⊔ P) :=
    isSylowOf_sup_of_coprime pPrimeCore_coprime_card hPp
  have heq : R ⊓ (pPrimeCore p H ⊔ P) = P :=
    hsyl.eq_of_le (le_inf hPR le_sup_right) inf_le_right (hR.to_le inf_le_left)
  intro s hs
  rw [← heq]
  exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hs,
    by rw [normalizer_eq_top]; exact mem_top s⟩

theorem isPStableWrt_of_dGroup (hp : p ≠ 2) (hst : DGroupStanding p H) {D R : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (hOp : pCore p H ≠ ⊥)
    (hcover : SignalizerCover (D.map (QuotientGroup.mk' (oddCore H))) ∨
      ¬ p ^ 2 ∣ Nat.card (H ⧸ oddCore H)) :
    IsPStableWrt p H R := by
  refine ⟨hOp, hR.1.1, hR.isSylowOf_inf_Op_p'p_of_le_oddCore hp hD hst.pPrimeCore_le,
    hR.normal_or_covers_of_oddCore hp hD hcover, ?_⟩
  intro P A _ hPR hn hAR hcomm
  have hRN := le_normalizer_of_le_of_sup_normal hR.1.1 hPR hn
  exact le_normalizerPCoreModCentralizer_of_isDGroup hp hst.isDGroup (hR.1.1.to_le hPR)
    (hR.1.1.to_le hAR) (hAR.trans hRN) hcomm

omit [Fact p.Prime] in
theorem signalizerCover_of_normal_eq_top {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hG : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → K = ⊤) : SignalizerCover D := by
  refine ⟨⊤, fun K hK hK1 => (hG K hK hK1).ge, fun X _ hDX => ⟨X, le_rfl, ‹_›, hDX, ?_⟩⟩
  rw [top_sup_eq, index_top]
  norm_num

section Wreathed

omit [Fact p.Prime] in
theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (oddCore X).map e.toMonoidHom = oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(oddCore_normal X).map _ e.surjective,
      by rw [card_map_of_injective e.injective]; exact odd_card_oddCore⟩
  · have hle : (oddCore Y).map e.symm.toMonoidHom ≤ oddCore X :=
      le_sSup ⟨(oddCore_normal Y).map _ e.symm.surjective,
        by rw [card_map_of_injective e.symm.injective]; exact odd_card_oddCore⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

omit [Fact p.Prime] in
theorem oddCore_quotient_oddCore_eq_bot : oddCore (H ⧸ oddCore H) = ⊥ := by
  set N := (oddCore (H ⧸ oddCore H)).comap (QuotientGroup.mk' (oddCore H)) with hN
  have hNn : N.Normal := (oddCore_normal _).comap _
  have hNodd : Odd (Nat.card N) := by
    rw [hN, card_comap_mk']
    exact odd_card_oddCore.mul odd_card_oddCore
  have hNO : N ≤ oddCore H := le_oddCore_of_normal hNn hNodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have : h ∈ oddCore H := hNO hx
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact this

theorem not_sq_dvd_card_quotient_oddCore_of_wreathed (hp : p ≠ 2) (hH : IsDGroup H) {n : ℕ}
    (hW : HasWreathedSylow H n) : ¬ p ^ 2 ∣ Nat.card (H ⧸ oddCore H) := by
  have hpp : p.Prime := Fact.out
  rcases hH with ⟨hDih, -⟩ | ⟨K, hK⟩
  · exact (not_hasWreathedSylow_and_dihedral hW hDih).elim
  obtain ⟨hK', hW'⟩ := CFSG.ABGDGroups.isDGroupData_quotient_oddCore hK hW
  let e : Shrink.{0} (H ⧸ oddCore H) ≃* H ⧸ oddCore H := Shrink.mulEquiv
  have : Finite (Shrink.{0} (H ⧸ oddCore H)) := Finite.of_equiv _ e.toEquiv.symm
  have hO₀ : oddCore (Shrink.{0} (H ⧸ oddCore H)) = ⊥ := by
    rw [← oddCore_map_mulEquiv e.symm, oddCore_quotient_oddCore_eq_bot, Subgroup.map_bot]
  obtain ⟨U, -, -, ⟨eU⟩, -, -, hU6, -⟩ := CFSG.ABGDGroups.wreathed_dGroup_structure hO₀
    (hK'.map_mulEquiv e.symm) (hW'.of_mulEquiv e.symm)
  have hcard : Nat.card (H ⧸ oddCore H) = 3 * 2 ^ (2 * n + 1) := by
    rw [← Nat.card_congr e.toEquiv, ← U.card_mul_index, hU6, Nat.card_congr eU.toEquiv,
      Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    ring
  rw [hcard]
  intro hd
  have hcop : Nat.Coprime (p ^ 2) (2 ^ (2 * n + 1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp Nat.prime_two).mpr hp)
  have h3 : p ^ 2 ∣ 3 := hcop.dvd_of_dvd_mul_right hd
  have := Nat.le_of_dvd (by norm_num) h3
  have h2 := hpp.two_le
  nlinarith

end Wreathed

end CFSG.ABGLocalTools
